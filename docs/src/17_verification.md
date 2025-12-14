# Software Verification

The promise of theorem provers extends beyond mathematics. We can verify that software does what we claim it does. This chapter builds a small interpreter for an expression language and proves properties about compiler optimizations. The techniques scale to real systems: verified compilers, operating system kernels, and cryptographic protocols.

## Intrinsically-Typed Interpreters

The standard approach to building interpreters involves two phases. First, parse text into an untyped abstract syntax tree. Second, run a type checker that rejects malformed programs. This works, but the interpreter must still handle the case where a program passes the type checker but evaluates to nonsense. The runtime carries the burden of the type system's failure modes.

Intrinsically-typed interpreters take a different approach. The abstract syntax tree itself encodes typing judgments. An ill-typed program cannot be constructed. The type system statically excludes runtime type errors, not by checking them at runtime, but by making them unrepresentable.

Consider a small expression language with natural numbers, booleans, arithmetic, comparisons, and let-bindings. We start by defining the types our language supports and a denotation function that maps them to Lean types.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:types}}
```

The `denote` function is key. It interprets our object-level types (`Ty`) as meta-level types (`Type`). When our expression language says something has type `nat`, we mean it evaluates to a Lean `Nat`. When it says `bool`, we mean a Lean `Bool`. This type-level interpretation function is what makes the entire approach work.

## Contexts and Variables

Variables in a typed language require tracking what types are in scope. We represent a typing context as a list of types, with the most recently bound variable at the head. Variables themselves are de Bruijn indices: proofs that a type exists at some position in the context.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:context}}
```

The `Var` type is indexed by both a context and a type. A value of type `Var ctx t` is a proof that type `t` appears in context `ctx`. The constructor `zero` witnesses that the head of the context has the expected type. The constructor `succ` witnesses that if a variable exists in the tail of a context, it also exists when we add a new binding.

Environments are runtime values corresponding to typing contexts. Where `Ctx` is a list of types, `Env ctx` is a nested tuple holding values of those types. Looking up a variable in an environment extracts the value at the corresponding position.

## Expressions

The expression type indexes over both context and result type. Each constructor precisely constrains which expressions can be built and what types they produce.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:expr}}
```

Every constructor documents its typing rule. The `add` constructor requires both arguments to be natural number expressions and produces a natural number expression. The `ite` constructor requires a boolean condition and two branches of matching type. The `let_` constructor extends the context for the body.

This encoding makes ill-typed expressions unrepresentable. You cannot write `add (nat 1) (bool true)` because the types do not align. The Lean type checker rejects such expressions before they exist.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:impossible}}
```

## Evaluation

The evaluator maps expressions to their denotations. Because expressions are intrinsically typed, the evaluator is total. It never fails, never throws exceptions, never encounters "impossible" cases. Every pattern match is exhaustive.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:eval}}
```

The return type `t.denote` varies with the expression's type index. A natural number expression evaluates to `Nat`. A boolean expression evaluates to `Bool`. This dependent return type is what makes the evaluator type-safe by construction.

Some examples demonstrate the evaluator in action.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:examples}}
```

## Verified Optimization

Interpreters become interesting when we transform programs. A constant folder simplifies expressions by evaluating constant subexpressions at compile time. Adding two literal numbers produces a literal. Conditionals with constant conditions eliminate the untaken branch.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:constfold}}
```

The optimization preserves types. If `e : Expr ctx t`, then `e.constFold : Expr ctx t`. The type indices flow through unchanged. This is not a dynamic property we hope holds. It is a static guarantee enforced by the type system.

But type preservation is a weak property. We want semantic preservation: the optimized program computes the same result as the original. This requires a proof.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:correctness}}
```

The theorem states that for any expression and any environment, evaluating the constant-folded expression yields the same result as evaluating the original. The proof proceeds by structural induction on the expression. Most cases follow directly from the induction hypotheses. The interesting cases are `add`, `mul`, and `ite`, where we split on whether the constant folding rule applied.

## Why This Matters

The techniques demonstrated here scale to real verification projects. The CompCert verified C compiler uses intrinsically-typed intermediate representations and proves semantic preservation across twenty compilation passes. The seL4 verified microkernel proves functional correctness of 10,000 lines of C code against a high-level specification.

The pattern is always the same. Embed the semantics of your system in a theorem prover. State the properties you care about. Prove them. The proofs may be tedious, but they are machine-checked. No amount of testing can provide the same guarantees.

When your system handles money, medical devices, or cryptographic secrets, the investment in formal verification pays for itself. One proof eliminates entire classes of bugs. The type system prevents you from even stating ill-typed programs. The theorem prover prevents you from claiming properties that do not hold.

The gap between verified kernel and production system remains real. Bisimulation techniques can bridge this gap, relating an efficient unverified implementation to a verified specification. The verified specification serves as an oracle. When both systems agree on all observable behaviors, the unverified implementation inherits the specification's guarantees. This remains an active research area, and Lean is well-positioned to contribute.
