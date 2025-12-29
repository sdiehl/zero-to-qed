# Software Verification

The promise of theorem provers extends beyond mathematics. We can verify that software does what we claim it does. This article explores three approaches to software verification: an intrinsically-typed interpreter where type safety is baked into the structure, Conway's Game of Life where we prove that gliders glide and blinkers blink, and finally verification-guided development where we transcribe Rust code into Lean and prove properties that transfer back to the production implementation.

## Intrinsically-Typed Interpreters

The standard approach to building interpreters involves two phases. First, parse text into an untyped abstract syntax tree. Second, run a type checker that rejects malformed programs. This works, but the interpreter must still handle the case where a program passes the type checker but evaluates to nonsense. The runtime carries the burden of the type system's failure modes. It is like a bouncer who checks IDs at the door but still has to deal with troublemakers inside.

**Intrinsically-typed interpreters** refuse to play this game. The abstract syntax tree itself encodes typing judgments. An ill-typed program cannot be constructed. The type system statically excludes runtime type errors, not by checking them at runtime, but by making them unrepresentable. The bouncer is replaced by architecture: there is no door for troublemakers to enter.

Consider a small expression language with natural numbers, booleans, arithmetic, and conditionals. We start by defining the types our language supports and a **denotation function** that maps them to Lean types.

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

## A Verified Compiler

The intrinsically-typed interpreter demonstrates type safety. But real systems compile to lower-level representations. Can we verify the compiler itself? The answer is yes, and it requires remarkably little code. In roughly 40 lines, we can define a source language, a target language, compilation, and prove the compiler correct. This is CompCert in miniature.

The source language is arithmetic expressions: literals, addition, and multiplication. The target language is a stack machine with push, add, and multiply instructions. The compilation strategy is straightforward: literals become pushes, binary operations compile their arguments and then emit the operator.

```lean
{{#include ../../src/ZeroToQED/Compiler.lean:verified_compiler}}
```

The key insight is the `run_append` lemma: executing concatenated instruction sequences is equivalent to executing them in order. This lets us prove correctness compositionally. The main theorem, `compile_correct`, states that running compiled code pushes exactly the evaluated result onto the stack.

The proof proceeds by structural induction on expressions. Literal compilation is trivially correct. For binary operations, we use `run_append` to split the execution: first we run the compiled left argument, then the compiled right argument, then the operator. The induction hypotheses tell us each subexpression evaluates correctly. The operator instruction combines them as expected.

```lean
{{#include ../../src/ZeroToQED/Compiler.lean:compiler_demo}}
```

This is verified compiler technology at its most distilled. The same principles scale to CompCert, which verifies a production C compiler. The gap between 40 lines and 100,000 lines is mostly the complexity of real languages and optimizations, not the verification methodology.

## Proof-Carrying Parsers

The intrinsically-typed interpreter guarantees type safety. The verified compiler guarantees semantic preservation. But what about parsers? A parser takes untrusted input and produces structured data. The traditional approach is to hope the parser is correct and test extensively. The verified approach is to make the parser carry its own proof of correctness.

A **proof-carrying parser** returns not just the parsed result but also evidence that the result matches the grammar. Invalid parses are not runtime errors; they are type errors. The proof is constructed during parsing and verified by the type checker.

We define a grammar as an inductive type with constructors for characters, sequencing, alternation, repetition, and the empty string:

```lean
{{#include ../../src/Examples/ParserCombinators.lean:grammar}}
```

The `Matches` relation defines when a string matches a grammar. Each constructor corresponds to a grammar production: a character matches itself, sequences match concatenations, alternatives match either branch, and repetition matches zero or more occurrences.

A parse result bundles the consumed input, remaining input, and a proof that the consumed portion matches the grammar:

```lean
{{#include ../../src/Examples/ParserCombinators.lean:parser}}
```

The parser combinators construct these proof terms as they parse. When `pchar 'a'` succeeds, it returns a `ParseResult` containing proof that `'a'` matches `Grammar.char 'a'`. When `pseq` combines two parsers, it combines their proofs using the `Matches.seq` constructor:

```lean
{{#include ../../src/Examples/ParserCombinators.lean:combinators}}
```

Soundness is trivial. Every successful parse carries its proof:

```lean
{{#include ../../src/Examples/ParserCombinators.lean:soundness}}
```

The theorem says: if a parser returns a result, then the consumed input matches the grammar. The proof is the identity function, because the evidence is already in the result. This is the power of proof-carrying data: correctness is not something we prove after the fact but something we construct alongside the computation.

## Conway's Game of Life

Before we tackle the challenge of connecting proofs to production code, let us take a detour through cellular automata. Conway's Game of Life is a zero-player game that evolves on an infinite grid. Each cell is either alive or dead. At each step, cells follow simple rules based on the eight neighbors surrounding each cell:

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

The answer comes from **verification-guided development**. The approach has three components. First, write the production implementation in your target language. Second, transcribe the core logic into Lean as a pure functional program. Third, prove properties about the Lean model; the proofs transfer to the production code because the transcription is exact. This technique was [developed by AWS for their Cedar policy language](https://arxiv.org/abs/2407.01688), and it applies wherever a functional core can be isolated from imperative scaffolding.

The transcription must be faithful. Every control flow decision in the Rust code must have a corresponding decision in the Lean model. Loops become recursion. Mutable state becomes accumulator parameters. Early returns become validity flags. When the transcription is exact, we can claim that the Lean proofs apply to the Rust implementation.

To verify this correspondence, both systems produce **execution traces**. A trace records the state after each operation. If the Rust implementation and the Lean model produce identical traces on all inputs, the proof transfers. For finite input spaces, we can verify this exhaustively. For infinite spaces, we use **differential testing** to gain confidence.

## The Stack Machine

We demonstrate verification with a stack machine, the fruit fly of computer science. Like the fruit fly in genetics, stack machines are simple enough to study exhaustively yet complex enough to exhibit interesting behavior. The machine has five operations: push a value, pop the top, add the top two values, multiply them, or duplicate the top.

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:ops}}
```

The `run` function executes a program against a stack:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:run}}
```

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:examples}}
```

## Universal Properties

The power of theorem proving lies not in verifying specific programs but in proving properties about all programs. Consider the composition theorem: running two programs in sequence equals running their concatenation.

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:composition}}
```

This theorem quantifies over all programs `p1` and `p2` and all initial stacks `s`. The proof proceeds by induction on the first program, with case analysis on each operation and the stack state. The result is a guarantee that holds for the infinite space of all possible programs.

## Stack Effects

Each operation has a predictable effect on stack depth. Push and dup add one element; pop, add, and mul remove one (add and mul consume two and produce one). We can compute the total effect of a program statically:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:effect}}
```

The `effect_append` theorem proves that stack effects compose additively. If program `p1` changes the stack depth by `n` and `p2` changes it by `m`, then `p1 ++ p2` changes it by `n + m`. This is another universal property, holding for all programs.

## Program Equivalence

We can also prove that certain program transformations preserve semantics. Addition and multiplication are commutative, so swapping the order of pushes does not change the result:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:equivalence}}
```

These theorems justify program transformations. An optimizer that reorders pushes before adds is provably correct. The `dup_add_eq_double` and `dup_mul_eq_square` theorems show that `push n; dup; add` computes `2n` and `push n; dup; mul` computes `n²`. A compiler could use these equivalences for strength reduction.

## What We Proved

The stack machine demonstrates verification of universal properties. We proved:

1. **Composition**: Running concatenated programs equals sequential execution
2. **Effect additivity**: Stack effects compose predictably
3. **Commutativity**: Push order does not affect addition or multiplication
4. **Equivalences**: Certain instruction sequences compute the same result

These are not tests of specific programs. They are theorems about the entire space of programs. The composition theorem alone covers infinitely many cases that no test suite could enumerate. This is the difference between testing and proving: tests sample behavior, proofs characterize it completely.

## Closing Thoughts

Why do we prove properties rather than test for them? Rice's [Classes of Recursively Enumerable Sets and Their Decision Problems](https://www.ams.org/journals/tran/1953-074-02/S0002-9947-1953-0053041-6/) provides the fundamental answer: every non-trivial semantic property of programs is undecidable. You cannot write a program that decides whether other programs halt, are correct, never access null, or satisfy any interesting behavioral property. The proof reduces from the halting problem. Verification escapes this limitation by requiring human-provided proofs that the compiler can check, rather than trying to infer properties automatically.

Finding good verification examples is hard. The system must be small enough to specify cleanly, complex enough to have non-trivial properties, and simple enough that proofs are tractable. Too simple and the exercise is pointless; too complex and the proofs become intractable. The stack machine threads this needle. Six operations, a validity flag, and stack depth create enough complexity for interesting proofs without overwhelming the verification machinery.

The `native_decide` tactic makes finite verification automatic. For any decidable property on a finite domain, Lean evaluates both sides and confirms equality. This is proof by exhaustive computation, not sampling. The limitation is that it only works for concrete inputs. Universal statements over infinite domains require structural induction.

The key insight is that we do not verify the Rust code directly. Rust's ownership system, borrow checker, and imperative features make direct verification impractical. Instead, we carve out the functional core, transcribe it to Lean, prove properties there, and transfer the proofs back through trace equivalence. The verification gap closes not through tool support, but through disciplined transcription and differential testing.

The techniques scale far beyond toy examples. Financial systems are a particularly compelling domain: matching engines, auction mechanisms, and clearing systems where bugs can trigger flash crashes or expose participants to unbounded losses. [Expressive bidding](https://www.onechronos.com/documentation/expressive/), where market orders encode complex preferences over combinations of instruments, requires solvers for NP-hard optimization problems with precise economic properties. These mechanisms must satisfy strategy-proofness and efficiency; the theorems exist in papers, and the implementations exist in production. Verification-guided development bridges them. Somewhere, proven-correct code is already running markets.
