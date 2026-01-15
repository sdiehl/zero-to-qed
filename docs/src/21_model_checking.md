# Model Checking

The [previous article](./20_verified_programs.md) demonstrated verification techniques where everything lives within Lean. But real systems are not written in Lean. They are written in Rust, C, Go, or whatever language the team knows and the platform demands. The gap between a verified model and a production implementation is where bugs hide. A correct specification means nothing if the implementation diverges from it.

This article explores how to bridge that gap using bounded model checking and verification-guided development.

## Conway's Game of Life

To see the verification gap in concrete terms, consider Conway's Game of Life. It is a zero-player game that evolves on an infinite grid. Each cell is either alive or dead. At each step, cells follow simple rules based on the eight neighbors surrounding each cell:

<figure style="text-align: center; margin: 1.5em 0;">
  <img src="./images/gol_neighbors.svg" alt="Cell neighbors" style="max-width: 100px;">
  <figcaption><em>Each cell has eight neighbors.</em></figcaption>
</figure>

The rules are simple. A live cell with two or three neighbors survives. A dead cell with exactly three neighbors becomes alive. Everything else dies. From these rules emerges startling complexity: oscillators, spaceships, and patterns that compute arbitrary functions.

The Game of Life is an excellent verification target because we can prove properties about specific patterns without worrying about the infinite grid. The challenge is that the true Game of Life lives on an unbounded plane, which we cannot represent directly. We need a finite approximation that preserves the local dynamics.

The standard solution is a toroidal grid. Imagine taking a rectangular grid and gluing the top edge to the bottom edge, forming a cylinder. Then glue the left edge to the right edge, forming a torus. Geometrically, this is the surface of a donut. A cell at the right edge has its eastern neighbor on the left edge. A cell at the top has its northern neighbor at the bottom. Every cell has exactly eight neighbors, with no special boundary cases.

This topology matters for verification. On a bounded grid with walls, edge cells would have fewer neighbors, changing their evolution rules. We would need separate logic for corners, edges, and interior cells. The toroidal topology eliminates this complexity: the neighbor-counting function is uniform across all cells. More importantly, patterns that fit within the grid and do not interact with their wrapped-around selves behave exactly as they would on the infinite plane. A 5x5 blinker on a 10x10 torus evolves identically to a blinker on the infinite grid, because the pattern never grows large enough to meet itself coming around the other side.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:grid}}
```

The grid representation uses arrays of arrays, with accessor functions that handle boundary conditions. The `countNeighbors` function implements toroidal wrapping by computing indices modulo the grid dimensions.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:neighbors}}
```

The step function applies Conway's rules to every cell. The pattern matching encodes the survival conditions directly: a live cell survives with 2 or 3 neighbors, a dead cell is born with exactly 3 neighbors.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:step}}
```

Now for the fun part. We can define famous patterns and prove properties about them.

The **blinker** is a period-2 oscillator: three cells in a row that flip between horizontal and vertical orientations, then back again.

<figure style="text-align: center; margin: 1.5em 0;">
  <img src="./images/gol_blinker.svg" alt="Blinker oscillation" style="max-width: 400px;">
  <figcaption><em>The blinker oscillates between vertical and horizontal orientations.</em></figcaption>
</figure>

The **block** is a 2x2 square that never changes. Each live cell has exactly three neighbors, so all survive. No dead cell has exactly three live neighbors, so none are born.

<figure style="text-align: center; margin: 1.5em 0;">
  <img src="./images/gol_block.svg" alt="Block pattern" style="max-width: 150px;">
  <figcaption><em>The block is stable: it never changes.</em></figcaption>
</figure>

The **glider** is the star of our show. It is a spaceship: a pattern that translates across the grid. After four generations, the glider has moved one cell diagonally.

<figure style="text-align: center; margin: 1.5em 0;">
  <img src="./images/gol_glider.svg" alt="Glider evolution" style="max-width: 100%;">
  <figcaption><em>The glider translates diagonally after four generations.</em></figcaption>
</figure>

After generation 4, the pattern is identical to generation 0, but shifted one cell down and one cell right. The glider crawls across the grid forever.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:patterns}}
```

Here is where theorem proving earns its keep. We can prove that the blinker oscillates with period 2, that the block is stable, and that the glider translates after exactly four generations.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:proofs}}
```

The `native_decide` tactic does exhaustive computation. Lean evaluates the grid evolution and confirms the equality. The proof covers every cell in the grid across the specified number of generations.

We have formally verified that a glider translates diagonally after four steps. Every cellular automaton enthusiast knows this empirically, having watched countless gliders march across their screens. But we have proven it. The glider must translate. It is not a bug that the pattern moves; it is a theorem. (Readers of Greg Egan's [Permutation City](https://en.wikipedia.org/wiki/Permutation_City) may appreciate that we are now proving theorems about the computational substrate in which his characters would live.)

We can also verify that the blinker conserves population, and observe that the glider does too:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:conservation}}
```

For visualization, we can print the grids:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:display}}
```

### The Gap Made Concrete

Here is the sobering reality. We have a beautiful proof that gliders translate. The Lean model captures Conway's rules precisely. The theorems are watertight. And yet, if someone writes a Game of Life implementation in Rust, our proofs say nothing about it.

The Rust implementation in `examples/game-of-life/` implements the same rules. It has the same step function, the same neighbor counting, the same pattern definitions. Run it and you will see blinkers blink and gliders glide. But the Lean proofs do not transfer automatically. The Rust code might have off-by-one errors in the wrap-around logic. It might use different integer semantics. It might have subtle bugs in edge cases that our finite grid proofs never exercise.

This is the central problem of software verification. Writing proofs about mathematical models is satisfying but insufficient. Real software runs on real hardware with real bugs. The gap matters most where the stakes are highest: matching engines that execute trades, auction mechanisms that allocate resources, systems where a subtle bug can cascade into market-wide failures.

How do we bridge the gap between a verified model and a production implementation?

## Verification-Guided Development

The answer comes from **verification-guided development**. The approach has three components. First, write the production implementation in your target language. Second, transcribe the core logic into Lean as a pure functional program. Third, prove properties about the Lean model; the proofs transfer to the production code because the transcription is exact. This technique was [developed by AWS for their Cedar policy language](https://arxiv.org/abs/2407.01688), and it applies wherever a functional core can be isolated from imperative scaffolding.

The transcription must be faithful. Every control flow decision in the Rust code must have a corresponding decision in the Lean model. Loops become recursion. Mutable state becomes accumulator parameters. Early returns become validity flags. When the transcription is exact, we can claim that the Lean proofs apply to the Rust implementation.

To verify this correspondence, both systems produce **execution traces**. A trace records the state after each operation. If the Rust implementation and the Lean model produce identical traces on all inputs, the proof transfers. For finite input spaces, we can verify this exhaustively. For infinite spaces, we can sometimes prove that bounded testing implies unbounded correctness, as we will see with the circuit breaker's uniformity theorem.

## Bounded Model Checking

Many real systems require state machines with complex transition rules: network protocols, payment processing, order lifecycles, and resilience patterns. How do we connect a verified Lean model to a production Rust implementation with strong guarantees?

The **circuit breaker** pattern prevents cascading failures in distributed systems. When a service starts failing, the circuit breaker "trips open" to block requests, giving the service time to recover. After a timeout, it allows a test request through. If the test succeeds, the circuit closes and normal operation resumes. If the test fails, the circuit stays open.

<figure style="text-align: center; margin: 1.5em 0;">
  <img src="./images/circuit_breaker.svg" alt="Circuit breaker state machine" style="max-width: 100%;">
  <figcaption><em>The circuit breaker state machine with three states and guarded transitions.</em></figcaption>
</figure>

The key insight is that each state carries different data. A closed breaker tracks failure count. An open breaker tracks when it opened (for timeout calculation). A half-open breaker needs no extra data.

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:config}}
```

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:state}}
```

Events trigger transitions between states:

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:event}}
```

## The Step Function

The entire verification approach centers on one function: `step`. This single function defines all circuit breaker behavior. Both Lean proofs and Rust verification target this exact definition.

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:step}}
```

This is the source of truth. Every property we prove, every test we run, every guarantee we claim flows from this definition. The function is pure, total, and deterministic.

## Proving Invariants

The state invariant says that closed circuits never accumulate failures beyond the threshold. Once failures reach the threshold, the circuit must trip open.

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:invariant}}
```

We prove specific transition properties too. Success resets failures. Reaching the threshold trips the circuit. The timeout transitions to half-open. These theorems are definitionally true, following directly from the structure of `step`:

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:theorems}}
```

## Predicate-Determined State Machines

Before presenting the main theorem, we need to understand why bounded testing can work at all for this system. The answer lies in a structural property: the circuit breaker is **predicate-determined**.

Look carefully at the `step` function. It makes exactly two comparisons: `failures + 1 >= threshold` (should the circuit trip?) and `time - openedAt >= timeout` (has the timeout elapsed?). Everything else is pattern matching on constructors. The function does not compute with the numeric values beyond these two boolean tests. It does not add timeout to threshold. It does not multiply failure counts. It does not branch on whether a timestamp is even or odd. The values flow through the function, but only these two predicates determine the control flow.

Contrast this with a function that lacks this structure:

```
step(count, Increment) = count + 1
```

Here the output depends on the magnitude of `count`, not just on a comparison. Testing with count=0, 1, 2, 3 tells us nothing about count=1000000. The function performs arithmetic that directly affects the output, creating infinitely many distinct behaviors.

The circuit breaker avoids this trap. When it stores `failures + 1` in the new state, that value flows through unchanged until the next comparison. The function never computes `failures * 2` or `threshold - failures`. Values are compared and stored, never combined arithmetically.

This structure has a profound consequence: if two inputs produce the same boolean comparison results, they must produce the same output constructor. With threshold=3 and failures=2, the comparison `failures + 1 >= threshold` yields `true`. With threshold=1000000 and failures=999999, the same comparison also yields `true`. Both inputs take the same branch. Both produce an `Open` state. The actual magnitudes do not matter; only the boolean outcomes do.

## The Uniformity Theorem

The predicate-determined structure enables a remarkable theorem. We formalize the observation above as the **uniformity theorem**. In equational form:

\\[
\text{kind}(s_1) = \text{kind}(s_2) \land \text{kind}(e_1) = \text{kind}(e_2) \land \text{cmp}(s_1, e_1) = \text{cmp}(s_2, e_2)
\\]
\\[
\implies \text{kind}(\text{step}(s_1, e_1)) = \text{kind}(\text{step}(s_2, e_2))
\\]

where \\(\text{kind}\\) extracts the constructor (Closed, Open, or HalfOpen) and \\(\text{cmp}\\) extracts the boolean comparison results. The theorem says: inputs that agree on structure and comparisons produce outputs that agree on structure.

Put simply: the function does not do math with the numbers, it just asks "is this bigger than that?" Once you have tested both "yes" and "no" for each question, you have tested everything.

**Proof sketch**: The proof proceeds in three steps. First, we case-split on the state constructors. If the two states have different constructors (say, one is `Closed` and one is `Open`), the hypothesis `sameStateKind s₁ s₂ = true` is false, giving an immediate contradiction. This eliminates all off-diagonal cases. Second, for each diagonal case (both `Closed`, both `Open`, or both `HalfOpen`), we case-split on event constructors. Again, mismatched events contradict `sameEventKind`. Third, we are left with only the cases where `step` actually branches: `(Closed, Failure)` which checks the threshold, and `(Open, Tick)` which checks the timeout. For these, we case-split on whether each comparison is true or false. The hypothesis `hsame_cmp` says the comparisons have the same boolean result, so if they disagree we have a contradiction. If they agree, both calls to `step` take the same branch and produce outputs with the same constructor.

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:uniformity}}
```

The theorem states: if two inputs have the same state kind (both `Closed`, both `Open`, or both `HalfOpen`), the same event kind, and the same comparison results, then the outputs have the same state kind. The proof proceeds by exhaustive case analysis on state and event constructors, then shows that matching comparison results force matching output constructors.

### Bounded Verification

The comparison outcomes partition the infinite input space into equivalence classes. All inputs where `failures + 1 >= threshold` is true behave identically (modulo the specific values stored). All inputs where it is false behave identically. Since there are only two comparisons, each boolean, there are at most four equivalence classes per (state kind, event kind) pair.

To verify the implementation for all inputs, we only need to test representatives from each equivalence class. A threshold of 3 with 2 failures represents all cases where the threshold is reached. A threshold of 3 with 0 failures represents all cases where it is not. Testing both covers the infinite space of threshold/failure combinations.

The uniformity theorem provides a mathematical proof that the equivalence classes are complete, eliminating sampling and heuristics. If an implementation passes tests covering all equivalence classes, it is correct for all inputs. Bounded testing with small values that hit both true and false for each comparison proves correctness for all values.

### Where Bounded Model Checking Applies

Many real-world state machines share this predicate-determined structure. _Protocol state machines_ like TCP transition based on flags and sequence number comparisons, not on packet payload arithmetic; a SYN-RECEIVED state becomes ESTABLISHED when ACK is set, regardless of sequence number magnitudes. _Business rule engines_ for order lifecycles (pending, confirmed, shipped, delivered) transition on event types and threshold comparisons like "payment received" or "inventory available," not on order total arithmetic. _Access control systems_ depend on role membership and policy predicates, not on computing with user IDs. _Rate limiters_ using token buckets transition on "tokens available >= cost" comparisons where the exact count matters only for that boolean test.

For any such system, bounded model checking can provide complete verification. The recipe is straightforward: identify all comparisons in the transition function, prove (or convince yourself) that behavior depends only on comparison outcomes, generate test cases covering all combinations of comparison outcomes, and verify the implementation against these cases.

### Where It Does Not Apply

The uniformity property does not hold for systems where output depends on arithmetic over unbounded values. _Counters and accumulators_ that sum transaction amounts cannot be verified by bounded testing; the sum of [1, 2, 3] tells us nothing about [1000000, 2000000]. _Cryptographic functions_ like hashes and encryption depend intimately on bit-level arithmetic where small inputs reveal nothing about large ones. _Numerical algorithms_ involving floating-point, matrix operations, or differential equations have behaviors that depend on magnitude, precision, and numerical stability. _Recursive depth_ matters too: a function that changes behavior at depth 1000 cannot be verified by testing to depth 100. _Overflow-sensitive code_ is particularly treacherous; if the implementation uses fixed-width integers that overflow, the Lean model (using mathematical naturals) diverges at the overflow boundary, and bounded testing might miss the case entirely.

The uniformity theorem gives us a criterion: can you factor the transition function into (1) comparisons that produce booleans, and (2) value shuffling that stores results without arithmetic? If yes, bounded model checking works. If no, you need different techniques.

### The Deeper Principle

The uniformity theorem exemplifies a broader principle in verification: exploit structure to reduce infinite problems to finite ones.

> [!NOTE]
> **The key insight**: The circuit breaker's predicate-determined structure lets us collapse an infinite input space into finitely many equivalence classes. This is non-trivial and depends on the specific structure of this problem. Not all state machines admit such a reduction. The uniformity theorem is a precise statement of _why_ this particular system has this property: because `step` branches only on boolean comparisons, never on arithmetic over values. Systems that compute with their inputs (counters, accumulators, cryptographic functions) do not have this structure and cannot be verified this way.

Other structures enable other reductions:

- **Symmetry**: If a function treats all elements of a set uniformly, test one representative
- **Monotonicity**: If a function is monotonic, test boundary cases
- **Compositionality**: If a function composes smaller functions, verify the pieces

The art of verification is recognizing which structures your system has and exploiting them appropriately. For predicate-determined state machines, bounded model checking provides complete verification, justified by mathematical proof.

## Test Generation

The uniformity theorem justifies generating exhaustive test cases within bounds. We enumerate all states, events, and configurations:

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:bounds}}
```

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:testcase}}
```

This generates

\\[
\sum_{t=1}^{4} 10 \times (t + 22) \times 85 = 83{,}300
\\]

test cases: for each threshold \\(t\\), we have 10 timeouts, \\(t + 22\\) states (\\(t\\) closed states plus 21 open states plus half-open), and 85 events. Each test case records the expected output state computed by Lean's `step` function. These cases are exported to JSON for Rust consumption.

## The Rust Implementation

The Rust `step` function must exactly match Lean's semantics. This is the verified core:

```rust
{{#include ../../examples/circuit-breaker/src/lib.rs:step}}
```

Note the use of `saturating_sub` for the timeout check. Lean's natural number subtraction is saturating (returns 0 for negative results), so Rust must use the same semantics to match.

## The Typestate API

The Rust typestate pattern provides an ergonomic API with compile-time state transition safety. The key insight is that every method calls the verified `step` function internally:

```rust
{{#include ../../examples/circuit-breaker/src/lib.rs:record_failure}}
```

Invalid transitions are compile errors. You cannot call `record_failure` on a `CircuitBreaker<Open>`. You cannot call `check_timeout` on a `CircuitBreaker<Closed>`. The type system enforces the state machine protocol at compile time.

## Exhaustive Testing

The Rust test loads all 83,300 test cases and verifies exact correspondence:

```rust
{{#include ../../examples/circuit-breaker/src/lib.rs:exhaustive_test}}
```

The test performs exhaustive verification within bounds, covering every combination of (threshold 1-4, timeout 1-10, state, event). The uniformity theorem guarantees that if all bounded cases pass, the unbounded implementation is correct. The [full Rust source](https://github.com/sdiehl/zero-to-qed/blob/main/examples/circuit-breaker/src/lib.rs) is available on GitHub.

## Where Trust Lives

The verification pipeline has three stages, and each introduces its own risks. Understanding where trust lies is essential to assessing the strength of the overall guarantee.

### Model and Transcription Risk

The Lean model must faithfully capture the intent of the Rust implementation. Unlike systems like CompCert or Coq's extraction mechanism, there is no automatic verified extraction from Lean to Rust. The correspondence relies on manual transcription. If the programmer makes a mistake in the transcription, a correct Lean proof says nothing about the incorrect Rust code.

The typestate API adds another layer. The ergonomic wrapper around the verified `step` function is verified only through unit tests, not exhaustive model checking. A bug in how the wrapper invokes `step` would compromise the guarantee.

### Execution Equivalence Risk

Rust and Lean have different runtime semantics. Rust's `saturating_sub` matches Lean's natural number subtraction, but this correspondence is verified by testing, not by formal proof. A different integer type or subtraction operation could break the equivalence silently.

Integer overflow is particularly treacherous. Lean uses unbounded natural numbers; Rust uses fixed-width integers. If the implementation overflows where the model does not, bounded testing might miss the divergence entirely. The circuit breaker avoids this by keeping all values small, but the risk remains for systems with larger numeric ranges.

### Testing Infrastructure Risk

The verification pipeline includes components that must simply be trusted: the JSON serialization layer that exports test cases from Lean, the serde deserialization that reads them in Rust, and the file I/O that moves data between systems. A bug in any of these components could cause false positives, reporting that tests pass when the implementations actually diverge.

### Defense in Depth

Despite these risks, the approach provides strong guarantees through layered defenses. The Lean model is provably correct: invariant preservation and the uniformity theorem are machine-checked proofs. The Rust `step` function is verified against 83,300 exhaustive test cases. The typestate API prevents invalid transitions at compile time. No single layer is impenetrable, but an attacker (or a bug) would need to defeat multiple independent mechanisms to produce an incorrect result.

The conjunction of all guarantees is captured in a single metatheorem:

```lean
{{#include ../../src/ZeroToQED/CircuitBreaker.lean:correctness}}
```

This theorem is the "golden assertion" of the circuit breaker: the initial state is valid, every transition preserves validity, and behavior depends only on comparison outcomes. If this theorem compiles, the model is correct.

## Closing Thoughts

Why do we prove properties rather than test for them? Rice's [Classes of Recursively Enumerable Sets and Their Decision Problems](https://www.ams.org/journals/tran/1953-074-02/S0002-9947-1953-0053041-6/) provides the fundamental answer: every non-trivial semantic property of programs is undecidable. You cannot write a program that decides whether other programs halt, are correct, never access null, or satisfy any interesting behavioral property. The proof reduces from the halting problem. Verification escapes this limitation by requiring human-provided proofs that the compiler can check, rather than trying to infer properties automatically.

The examples in this series form a hierarchy of verification strength, from weakest to strongest:

- **Game of Life**: `native_decide` exhaustively checks specific finite patterns (gliders glide, blinkers blink), but the guarantees cover only those patterns and only the Lean model.
- **Proof-carrying parsers**: Soundness by construction within Lean, with evidence built alongside computation, though again confined to the Lean model.
- **Intrinsically-typed interpreter**: Ill-typed programs are unrepresentable, a structural guarantee that eliminates entire classes of bugs but only within Lean's type system.
- **Verified compiler**: Semantic preservation universally over all expressions; compiled code produces the same result as interpretation. A stronger claim that quantifies over infinite inputs but remains Lean-only.
- **Stack machine**: Universal theorems (composition, commutativity, effect additivity) quantify over infinite program spaces with no external transfer.
- **Circuit breaker**: The uniformity theorem mathematically justifies that bounded testing covers unbounded inputs, enabling Lean proofs to transfer to a Rust implementation via exhaustive model checking. Only this example bridges the verification gap to production code.

Each example illustrates a different verification technique. The Game of Life and verified compiler use `native_decide` for exhaustive finite computation: Lean evaluates both sides and confirms equality, proof by brute force rather than insight. The stack machine uses structural induction to prove universal properties over infinite program spaces. The circuit breaker combines both: structural induction proves the uniformity theorem, which then justifies exhaustive finite testing as a complete verification technique.

The circuit breaker also demonstrates verification-guided development: we do not verify the Rust code directly. Rust's ownership system, borrow checker, and imperative features make direct verification impractical. Instead, we carve out the functional core, transcribe it to Lean, prove properties there, and transfer the proofs back through exhaustive testing. The verification gap closes through disciplined transcription and bounded model checking justified by mathematical proof.

The techniques scale far beyond toy examples. Financial systems are a particularly compelling domain: matching engines, order books, and clearing systems where bugs can trigger flash crashes or expose participants to unbounded losses. Trading systems are state machines at heart, and the state machines that move money tend to be predicate-determined in exactly the way that makes bounded model checking viable. The theorems exist in papers, and the implementations exist in production. Verification-guided development bridges them.
