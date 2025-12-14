# Software Verification

The promise of theorem provers extends beyond mathematics. We can verify that software does what we claim it does. This chapter explores three approaches to software verification: an intrinsically-typed interpreter where type safety is baked into the structure, Conway's Game of Life where we prove that gliders glide and blinkers blink, and finally verification-guided development where we transcribe Rust code into Lean and prove properties that transfer back to the production implementation.

## Intrinsically-Typed Interpreters

The standard approach to building interpreters involves two phases. First, parse text into an untyped abstract syntax tree. Second, run a type checker that rejects malformed programs. This works, but the interpreter must still handle the case where a program passes the type checker but evaluates to nonsense. The runtime carries the burden of the type system's failure modes. It is like a bouncer who checks IDs at the door but still has to deal with troublemakers inside.

Intrinsically-typed interpreters refuse to play this game. The abstract syntax tree itself encodes typing judgments. An ill-typed program cannot be constructed. The type system statically excludes runtime type errors, not by checking them at runtime, but by making them unrepresentable. The bouncer is replaced by architecture: there is no door for troublemakers to enter.

Consider a small expression language with natural numbers, booleans, arithmetic, and conditionals. We start by defining the types our language supports and a denotation function that maps them to Lean types.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:types}}
```

The `denote` function is key. It interprets our object-level types (`Ty`) as meta-level types (`Type`). When our expression language says something has type `nat`, we mean it evaluates to a Lean `Nat`. When it says `bool`, we mean a Lean `Bool`. This type-level interpretation function is what makes the entire approach work.

## Expressions

The expression type indexes over the result type. Each constructor precisely constrains which expressions can be built and what types they produce.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:expr}}
```

Every constructor documents its typing rule. The `add` constructor requires both arguments to be natural number expressions and produces a natural number expression. The `ite` constructor requires a boolean condition and two branches of matching type.

This encoding makes ill-typed expressions unrepresentable. You cannot write `add (nat 1) (bool true)` because the types do not align. The Lean type checker rejects such expressions before they exist.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:impossible}}
```

## Evaluation

The evaluator maps expressions to their denotations. Because expressions are intrinsically typed, the evaluator is total. It never fails, never throws exceptions, never encounters impossible cases. Every pattern match is exhaustive.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:eval}}
```

The return type `t.denote` varies with the expression's type index. A natural number expression evaluates to `Nat`. A boolean expression evaluates to `Bool`. This dependent return type is what makes the evaluator type-safe by construction.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:examples}}
```

## Verified Optimization

Interpreters become interesting when we transform programs. Compilers do this constantly: dead code elimination, loop unrolling, strength reduction. Each transformation promises to preserve meaning while improving performance. But how do we know the promise is kept? A constant folder simplifies expressions by evaluating constant subexpressions at compile time. Adding two literal numbers produces a literal. Conditionals with constant conditions eliminate the untaken branch.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:constfold}}
```

The optimization preserves types. If `e : Expr t`, then `e.constFold : Expr t`. The type indices flow through unchanged. The type system enforces this statically.

But type preservation is a weak property. We want semantic preservation: the optimized program computes the same result as the original. This requires a proof.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:correctness}}
```

The theorem states that for any expression, evaluating the constant-folded expression yields the same result as evaluating the original. The proof proceeds by structural induction on the expression. Most cases follow directly from the induction hypotheses.

## Conway's Game of Life

Before we tackle the challenge of connecting proofs to production code, let us take a detour through cellular automata. Conway's Game of Life is a zero-player game that evolves on an infinite grid. Each cell is either alive or dead. At each step, cells follow simple rules: a live cell with two or three neighbors survives, a dead cell with exactly three neighbors becomes alive, and everything else dies. From these rules emerges startling complexity: oscillators, spaceships, and patterns that compute arbitrary functions.

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

Now for the fun part. We can define famous patterns and prove properties about them. The blinker is a period-2 oscillator: three cells in a row that flip between horizontal and vertical orientations. The block is a 2x2 square that never changes. And the glider, the star of our show, is a pattern that translates diagonally across the grid.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:patterns}}
```

Here is where theorem proving earns its keep. We can prove that the blinker oscillates with period 2, that the block is stable, and that the glider translates after exactly four generations.

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:proofs}}
```

The `native_decide` tactic does exhaustive computation. Lean evaluates the grid evolution and confirms the equality. The proof covers every cell in the grid across the specified number of generations.

Think about what we have accomplished. We have formally verified that a glider translates diagonally after four steps. Every cellular automaton enthusiast knows this empirically, having watched countless gliders march across their screens. But we have proven it. The glider must translate. It is not a bug that the pattern moves; it is a theorem. (Readers of Greg Egan's [Permutation City](https://en.wikipedia.org/wiki/Permutation_City) may appreciate that we are now proving theorems about the computational substrate in which his characters would live.)

We can also verify that the blinker conserves population, and observe that the glider does too:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:conservation}}
```

For visualization, we can print the grids:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:display}}
```

## The Verification Gap

Here is the sobering reality check. We have a beautiful proof that gliders translate. The Lean model captures Conway's rules precisely. The theorems are watertight. And yet, if someone writes a Game of Life implementation in Rust, our proofs say nothing about it.

The Rust implementation in `examples/game-of-life/` implements the same rules. It has the same step function, the same neighbor counting, the same pattern definitions. Run it and you will see blinkers blink and gliders glide. But the Lean proofs do not transfer automatically. The Rust code might have off-by-one errors in the wrap-around logic. It might use different integer semantics. It might have subtle bugs in edge cases that our finite grid proofs never exercise.

This is the central problem of software verification. Writing proofs about mathematical models is satisfying but insufficient. Real software runs on real hardware with real bugs. The gap matters most where the stakes are highest: matching engines that execute trades, auction mechanisms that allocate resources, systems where a subtle bug can cascade into market-wide failures. How do we bridge the gap between a verified model and a production implementation?

## Verification-Guided Development

The interpreter example shows verification within Lean. But real systems are written in languages like Rust, C, or Go. How do we connect a verified specification to a production implementation?

The answer comes from verification-guided development. The approach has three components. First, write the production implementation in your target language. Second, transcribe the core logic into Lean as a pure functional program. Third, prove properties about the Lean model; the proofs transfer to the production code because the transcription is exact. This technique was used by AWS to verify their Cedar policy language, and it applies wherever a functional core can be isolated from imperative scaffolding.

The transcription must be faithful. Every control flow decision in the Rust code must have a corresponding decision in the Lean model. Loops become recursion. Mutable state becomes accumulator parameters. Early returns become validity flags. When the transcription is exact, we can claim that the Lean proofs apply to the Rust implementation.

To verify this correspondence, both systems produce execution traces. A trace records the state after each operation. If the Rust implementation and the Lean model produce identical traces on all inputs, the proof transfers. For finite input spaces, we can verify this exhaustively. For infinite spaces, we use differential testing to gain confidence.

## The Stack Machine

We demonstrate this technique with a stack machine, the fruit fly of computer science. Like the fruit fly in genetics, stack machines are simple enough to study exhaustively yet complex enough to exhibit interesting behavior. The machine has six operations: push a value, pop the top, add the top two values, multiply the top two values, duplicate the top, and swap the top two. Despite its simplicity, the stack machine has a rich state space and non-trivial invariants around underflow detection.

The Rust implementation lives in `examples/stack-machine/`. Here is the functional core:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    pub stack: Vec<i64>,
    pub valid: bool,
}

pub fn step(state: &State, op: Op) -> State {
    if !state.valid {
        return State { stack: state.stack.clone(), valid: false };
    }

    match op {
        Op::Push(n) => {
            let mut stack = state.stack.clone();
            stack.push(n);
            State { stack, valid: true }
        }
        Op::Pop => {
            if state.stack.is_empty() {
                State { stack: state.stack.clone(), valid: false }
            } else {
                let mut stack = state.stack.clone();
                stack.pop();
                State { stack, valid: true }
            }
        }
        Op::Add => {
            if state.stack.len() < 2 {
                State { stack: state.stack.clone(), valid: false }
            } else {
                let mut stack = state.stack.clone();
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a + b);
                State { stack, valid: true }
            }
        }
        // Mul, Dup, Swap follow the same pattern
    }
}
```

The `step` function is pure despite using mutation internally. It takes a state and an operation, returns a new state. The `valid` flag tracks whether an underflow has occurred. Once invalid, the machine stays invalid regardless of subsequent operations. The machine remembers its sins.

## Lean Transcription

The Lean model mirrors the Rust implementation exactly. It is the implementation, translated. We define the same operations and state structure:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:ops}}
```

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:state}}
```

The step function transcribes the Rust logic line by line:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:step}}
```

Every branch in the Rust `match` corresponds to a branch in the Lean `match`. The underflow checks are identical. The stack operations map directly. It is the Rust code written in Lean syntax.

We also define execution functions:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:run}}
```

## Execution Traces

Both systems produce execution traces. The Lean trace function records the state before each operation:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:trace}}
```

Running traces shows the parallel execution:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:trace_examples}}
```

The trace for `[push 3, push 4, add]` produces:
```
[{ stack := [], valid := true },
 { stack := [3], valid := true },
 { stack := [4, 3], valid := true },
 { stack := [7], valid := true }]
```

The trace for `[pop]` (underflow) produces:
```
[{ stack := [], valid := true },
 { stack := [], valid := false }]
```

The Rust implementation produces identical traces. When we run the same programs through both systems and compare the output, every state matches exactly. This trace equivalence is what justifies transferring proofs from Lean to Rust.

## Bisimulation Proofs

Now we prove properties about specific programs. This is where the payoff arrives. These theorems verify that the Lean model produces the expected results:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:concrete_bisim}}
```

Each theorem states the exact final state after running a program. The `native_decide` tactic evaluates the computation and confirms the equality. These are not tests that sample the behavior; they are proofs that the computation produces this exact result.

We also verify the traces themselves:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:trace_bisim}}
```

The trace proofs verify the entire execution history, not just the final state. Every intermediate state is exactly what we claim.

## Invariant Proofs

Beyond concrete examples, we prove general properties. The underflow detection works correctly:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:underflow_proofs}}
```

The `invalid_propagates` theorem proves that once the machine enters an invalid state, it stays invalid. This is the critical safety property: underflow is detected and the machine does not produce garbage results.

We verify depth properties:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:bisim_basic}}
```

Push increases the stack depth by one. Add decreases it by one (consuming two elements, producing one). Swap preserves depth. These depth invariants ensure the machine behaves predictably.

## Verified Programs

Finally, we verify complete programs:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:verified_programs}}
```

Each program computes the correct result. The Rust implementation passes the same tests. Because the Lean model is an exact transcription of the Rust code, and we have proven properties about the Lean model, those properties apply to the Rust implementation.

## What We Proved

The stack machine demonstrates verification-guided development end to end. We have:

1. A production Rust implementation with mutation, pattern matching, and control flow
2. An exact Lean transcription that mirrors every decision
3. Execution traces showing both systems produce identical state sequences
4. Proofs that underflow is detected and propagates correctly
5. Proofs that specific programs compute expected results

The transcription discipline is essential. We did not write an independent specification and hope it matches. We wrote the Rust logic in Lean syntax, preserving the structure exactly. Loops became recursion with the same termination condition. Mutable state became parameters threaded through recursive calls. The `valid` flag in both implementations serves the same purpose: tracking whether an underflow has occurred.

This technique scales to real systems. For any codebase with a functional core that can be isolated and transcribed, verification-guided development provides a path to proven correctness.

## Closing Thoughts

Finding good verification examples is hard. The system must be small enough to specify cleanly, complex enough to have non-trivial properties, and simple enough that proofs are tractable. Too simple and the exercise is pointless; too complex and the proofs become intractable. The stack machine threads this needle. Six operations, a validity flag, and stack depth create enough complexity for interesting proofs without overwhelming the verification machinery.

The `native_decide` tactic makes finite verification automatic. For any decidable property on a finite domain, Lean evaluates both sides and confirms equality. This is proof by exhaustive computation, not sampling. The limitation is that it only works for concrete inputs. Universal statements over infinite domains require structural induction.

The key insight is that we do not verify the Rust code directly. Rust's ownership system, borrow checker, and imperative features make direct verification impractical. Instead, we carve out the functional core, transcribe it to Lean, prove properties there, and transfer the proofs back through trace equivalence. The verification gap closes not through tool support, but through disciplined transcription and differential testing.

The techniques scale far beyond toy examples. CompCert verifies a C compiler. seL4 verifies an operating system kernel. Financial systems are a particularly compelling domain: matching engines, auction mechanisms, and clearing systems where bugs can trigger flash crashes or expose participants to unbounded losses. Expressive bidding, where market orders encode complex preferences over combinations of instruments, requires matching algorithms with precise economic properties. These mechanisms must satisfy strategy-proofness and efficiency; the theorems exist in papers, and the implementations exist in production. Verification-guided development bridges them. Somewhere beneath global markets, proven-correct code is already executing trades.
