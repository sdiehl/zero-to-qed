# Verified Programs

The promise of theorem provers extends beyond mathematics. We can verify that software does what we claim it does. This article demonstrates verification techniques where the verified code and the production code are the same: everything lives within Lean.

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

A **proof-carrying parser** returns both the parsed result and evidence that the result matches the grammar. Invalid parses become type errors rather than runtime errors. The proof is constructed during parsing and verified by the type checker.

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

The theorem says: if a parser returns a result, then the consumed input matches the grammar. The proof is the identity function, because the evidence is already in the result. Proof-carrying data constructs correctness alongside the computation rather than establishing it after the fact.

## The Stack Machine

We continue with another Lean-only verification example: a stack machine, the fruit fly of computer science. Like the fruit fly in genetics, stack machines are simple enough to study exhaustively yet complex enough to exhibit interesting behavior. The machine has five operations: push a value, pop the top, add the top two values, multiply them, or duplicate the top.

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

### Universal Properties

The power of theorem proving lies not in verifying specific programs but in proving properties about all programs. Consider the composition theorem: running two programs in sequence equals running their concatenation.

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:composition}}
```

This theorem quantifies over all programs `p1` and `p2` and all initial stacks `s`. The proof proceeds by induction on the first program, with case analysis on each operation and the stack state. The result is a guarantee that holds for the infinite space of all possible programs.

### Stack Effects

Each operation has a predictable effect on stack depth. Push and dup add one element; pop, add, and mul remove one (add and mul consume two and produce one). We can compute the total effect of a program statically:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:effect}}
```

The `effect_append` theorem proves that stack effects compose additively. If program `p1` changes the stack depth by `n` and `p2` changes it by `m`, then `p1 ++ p2` changes it by `n + m`. This is another universal property, holding for all programs.

### Program Equivalence

We can also prove that certain program transformations preserve semantics. Addition and multiplication are commutative, so swapping the order of pushes does not change the result:

```lean
{{#include ../../src/ZeroToQED/StackMachine.lean:equivalence}}
```

These theorems justify program transformations. An optimizer that reorders pushes before adds is provably correct. The `dup_add_eq_double` and `dup_mul_eq_square` theorems show that `push n; dup; add` computes `2n` and `push n; dup; mul` computes `n²`. A compiler could use these equivalences for strength reduction.

### What We Proved

The stack machine demonstrates verification of universal properties. We proved that running concatenated programs equals sequential execution (composition), that stack effects compose predictably (effect additivity), that push order does not affect addition or multiplication (commutativity), and that certain instruction sequences compute the same result (equivalences).

These theorems quantify over the entire space of programs, unlike tests of specific inputs. The composition theorem alone covers infinitely many cases that no test suite could enumerate. A passing test establishes an existential claim ("there exists an input where the program works"), while a theorem establishes a universal claim ("for all inputs, the program works"). Tests sample behavior, proofs characterize it completely.

## The Verification Gap

Everything so far lives entirely within Lean. The interpreter is correct by construction. The compiler preserves semantics. The parser carries its proof. The stack machine obeys universal laws. These are real theorems about real programs. And yet they share a fundamental limitation: the verified code and the production code are the same code. There is no gap to bridge because there is no bridge to cross.

Real systems are not written in Lean. They are written in Rust, C, Go, or whatever language the team knows and the platform demands. The [next article](./22_model_checking.md) explores how to bridge the gap between a verified model and a production implementation.
