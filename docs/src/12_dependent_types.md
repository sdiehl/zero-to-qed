# Dependent Types

Why bother with all this? The honest answer is that most working programmers will never need dependent types, the same way most drivers will never need to understand engine timing. The dishonest answer is that dependent types will make you more productive. The true answer is somewhere stranger: ordinary type systems cannot express the constraints that actually matter. You can say "this is a list" but not "this is a list of exactly five elements." You can say "this function returns an integer" but not "this function returns a positive integer smaller than its input." Every time you write a comment explaining what a function really does, every time you add a runtime check for an invariant the compiler cannot see, every time a bug slips through because the types were not precise enough, you are paying the cost of an insufficiently expressive type system. The comment is a wish. The runtime check is a prayer. Dependent types are a contract.

Dependent types are the solution. They let types talk about values. The type `Vector α 5` denotes a list of exactly five elements. The type `Fin n` represents a natural number provably less than `n`. Array bounds checking happens at compile time. Protocol state machines live in the types. The invariants you used to hope were true become things the compiler verifies.

[Per Martin-Löf](https://en.wikipedia.org/wiki/Per_Martin-L%C3%B6f) spent the 1970s in Sweden developing this type theory where types could depend on values, not just on other types. The idea seems simple enough: if `List` can be parameterized by an element type, why not also by its length? But this small step has profound consequences. Suddenly types become a specification language. A function returning `Vector α n` does not merely return a list; it returns a list of exactly `n` elements, verified at compile time. Polymorphic type systems like those in Haskell (built on [System FC](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/fc), an extension of System Fω with type equality coercions) and OCaml (an extended ML core with row polymorphism and first-class modules) stop at the water's edge here. Dependent types let you wade in, expressing invariants that would otherwise live only in documentation or runtime checks. Lean's type system, based on the [Calculus of Inductive Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions), provides the full machinery: types that compute, proofs that are programs, and specifications precise enough to replace testing with theorem proving.

> [!WARNING]
> This section is dense and notation-heavy. If the mathematical symbols start to blur together, that is not a personal failing. It is the appropriate response to notation that took logicians fifty years to stabilize and still varies between textbooks. Skip ahead and return later. Or don't. Some people read this material linearly, some spiral in from the edges, some open to random pages and see what sticks. There is no wrong way to learn type theory except to believe you should have understood it faster. The notation table below is a reference, not a prerequisite.

## Notation

| Concept              | Mathematical Notation               | Lean Syntax                | Description                                  |
| -------------------- | ----------------------------------- | -------------------------- | -------------------------------------------- |
| Function type        | $\alpha \to \beta$              | `α → β`                    | Non-dependent function from α to β           |
| Dependent function   | $\Pi (x : \alpha), \beta(x)$    | `(x : α) → β x`            | Function where return type depends on input  |
| For all              | $\forall x : \alpha, P(x)$      | `∀ x : α, P x`             | Universal quantification                     |
| Exists               | $\exists x : \alpha, P(x)$      | `∃ x : α, P x`             | Existential quantification                   |
| Lambda abstraction   | $\lambda x. t$                  | `fun x => t` or `λ x => t` | Anonymous function                           |
| Equivalence          | $a \equiv b$                    | N/A                        | Definitional equality                        |
| Conjunction          | $P \land Q$                     | `P ∧ Q`                    | Logical AND                                  |
| Disjunction          | $P \lor Q$                      | `P ∨ Q`                    | Logical OR                                   |
| Negation             | $\neg P$                        | `¬P`                       | Logical NOT                                  |
| Type universe        | $\text{Type}_n$                 | `Type n`                   | Universe of types at level n                 |
| Proposition universe | $\text{Prop}$                   | `Prop`                     | Universe of propositions                     |
| Sort hierarchy       | $\text{Sort}_n$                 | `Sort n`                   | Unified universe hierarchy                   |
| Quotient type        | $\alpha/{\sim}$                 | `Quotient s`               | Type obtained by quotienting α by relation ∼ |
| Natural numbers      | $\mathbb{N}$                    | `Nat` or `ℕ`               | Natural numbers type                         |
| Integers             | $\mathbb{Z}$                    | `Int` or `ℤ`               | Integer type                                 |
| Sigma type           | $\Sigma (x : \alpha), \beta(x)$ | `Σ x : α, β x`             | Dependent pair type                          |
| Product type         | $\alpha \times \beta$           | `α × β`                    | Cartesian product                            |

## Type System Overview

Lean's type system supports definitional equality through several reduction rules. Two terms are definitionally equal when one reduces to the other, and the type checker treats them as interchangeable without proof.

**Beta reduction** ($\beta$) is function application. When you apply $(\lambda x. t)$ to an argument $s$, the result is $t$ with $s$ substituted for $x$. This is the computational heart of the lambda calculus.

**Delta reduction** ($\delta$) unfolds definitions. When you define `def f x := x + 1`, any occurrence of `f 3` can be replaced with `3 + 1`. The type checker sees through your naming conventions.

**Iota reduction** ($\iota$) handles pattern matching on inductive types. When a recursor meets a constructor, the match fires and computation proceeds. This is how `Nat.rec` applied to `Nat.succ n` knows to take the successor branch.

**Zeta reduction** ($\zeta$) substitutes let-bound variables. The expression $\\text{let } x := s \\text{ in } t$ reduces to $t[s/x]$. Local definitions are just convenient names.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:type_system_overview}}
```

## Functions

Function types are a built-in feature of Lean. Functions map values from one type (the domain) to another type (the codomain). In Lean's core language, **all function types are dependent**. Non-dependent function types are just a special case where the parameter does not appear in the codomain.

### Non-Dependent vs Dependent Functions

**Non-dependent functions** have a fixed return type that does not vary based on the input value. These are the only kinds of functions available in languages like Haskell (`not :: Bool -> Bool`) and OCaml (`let not : bool -> bool`). In Lean, `def not : Bool → Bool` uses the arrow notation to indicate non-dependence. The return type is always `Bool`, regardless of which boolean you pass in.

**Dependent functions** have a return type that can depend on the actual value of the input. The type is written as $\\Pi (x : \\alpha), \\beta(x)$ or `(x : α) → β x` in Lean syntax, where the parameter name `x` appears in the return type `β x`. This feature has **no equivalent in Haskell or OCaml**.

Key insight: Dependent functions can return values from completely different types based on their input! This is sometimes called a **dependent product** because it corresponds to an indexed product of sets.

> [!TIP]
> The name "dependent product" may seem backwards since we are building functions, not pairs. The terminology comes from set theory: a function $f : \\Pi (x : A), B(x)$ assigns to each $x \\in A$ an element of $B(x)$, which is precisely an element of the Cartesian product $\\prod_{x \\in A} B(x)$. The "product" is over all possible inputs.

### Why Dependent Types Matter

Consider this function that cannot be typed in Haskell or OCaml:

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:dependent_return_type}}
```

The return type literally changes based on the runtime value. Call `two true` and you get a `Unit × Unit`. Call `two false` and you get a `String`. This should feel slightly transgressive. A function that returns different types? In most languages, this is either impossible or requires erasing all type information and hoping for the best. Here, the type system tracks it precisely. The function is total, the types are known, the compiler is satisfied.

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:dependent_pattern_matching}}
```

This enables encoding invariants directly in types. For example, `Vector α n` encodes the length `n` in the type itself, making it impossible to write functions that violate length constraints. Your off-by-one errors become compile-time errors. The compiler catches at build time what you would otherwise discover in production, at 3am, with the on-call phone ringing.

### Typing Rules for Functions

Two rules govern how types flow through function definitions and applications. The first is **application**: when you apply a function to an argument, the return type can mention the argument itself. If $f : \\Pi (x : \\alpha), \\beta(x)$ and you apply it to some $a : \\alpha$, the result $f \\, a$ has type $\\beta(a)$. The type of the output depends on the value of the input. This is the essence of dependent typing. A function `Vector.head : (n : Nat) → Vector α (n + 1) → α` applied to `3` yields a function expecting a `Vector α 4`. The `3` propagates into the type.

The second rule is **abstraction**: to construct a function, you assume a variable of the input type and produce a term of the output type. If $t : \\beta$ under the assumption $x : \\alpha$, then $\\lambda x : \\alpha. \\, t$ has type $\\Pi (x : \\alpha), \\beta$. The abstraction binds the variable and packages the assumption into the function type. When $\\beta$ does not mention $x$, this collapses to the familiar non-dependent arrow $\\alpha \\to \\beta$.

Beyond formation and elimination, functions satisfy **eta-reduction**: wrapping a function in a lambda that immediately applies it produces the same function. Formally, $\\lambda x. \\, f \\, x \\equiv f$ when $x$ does not appear free in $f$. This goes beyond simplification; it expresses extensionality: a function is determined by what it does to its arguments, not by how it is written.

### Examples: Dependent and Non-Dependent Functions

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_dependent}}
```

### Currying

Currying is the fundamental technique of transforming functions with multiple parameters into sequences of single-parameter functions. Named after logician [Haskell Curry](https://en.wikipedia.org/wiki/Haskell_Curry) (yes, the programming language is also named after him), this approach is automatic in Lean. All multi-parameter functions are internally represented as curried functions. This enables partial application, where supplying fewer arguments than a function expects creates a new function waiting for the remaining arguments.

> [!NOTE]
> The technique was actually discovered by Moses Schonfinkel in 1924, six years before Curry's work. Academic naming conventions are not always fair. Schonfinkel's life ended in obscurity in a Moscow hospital; Curry became a household name among programmers who have never heard of either.

The power of currying lies in its composability. You can create specialized functions by partially applying general ones, building up complex behavior from simple building blocks. While languages like Haskell make currying explicit, Lean handles it transparently, allowing you to work with multi-parameter functions naturally while still benefiting from the flexibility of curried representations.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_currying}}
```

### Function Extensionality

Function extensionality is a fundamental principle stating that two functions are equal if and only if they produce equal outputs for all equal inputs. This principle, while intuitively obvious, is not derivable from the other axioms of dependent type theory and must be added as an axiom in Lean. Without extensionality, we could only prove functions equal if they were syntactically identical: the same symbols in the same order.

The `funext` tactic in Lean implements this principle, allowing us to prove function equality by considering their behavior pointwise. This is essential for mathematical reasoning, where we often want to show that two different definitions actually describe the same function. The principle extends to dependent functions as well, where the output type can vary with the input.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_extensionality}}
```

### Totality and Termination

> [!IMPORTANT]
> All functions in Lean must be total, meaning they must be defined for every possible input of the correct type. This requirement ensures logical consistency: a function that could fail or loop forever would make Lean's logic unsound. Partiality is the enemy. The function that hangs on edge cases, the recursion that never terminates, the match that forgot a constructor: these are not just bugs but logical contradictions waiting to invalidate your theorems.

To achieve totality while allowing recursion, Lean uses well-founded recursion based on decreasing measures.

For structural recursion on inductive types, Lean automatically proves termination by observing that recursive calls operate on structurally smaller arguments. For more complex recursion patterns, you can specify custom termination measures using `termination_by` and provide proofs that these measures decrease with `decreasing_by`. This approach allows expressing any computable function while maintaining logical soundness. If you have ever written `while (true)` and hoped for the best, this is the universe collecting on that debt.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_totality}}
```

For non-structural recursion, you must provide a termination measure that decreases on each recursive call. The classic examples are the GCD algorithm (where the second argument decreases) and the Ackermann function (where the lexicographic pair decreases):

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:termination}}
```

### Function API Reference

Lean's standard library provides a rich collection of function combinators in the `Function` namespace. These combinators, familiar from functional programming, enable point-free style and function composition. The composition operator `∘` allows building complex functions from simpler ones, while combinators like `const`, `flip`, and `id` provide basic building blocks for function manipulation.

Function composition in Lean satisfies the expected mathematical properties: it is associative, and the identity function acts as a neutral element. These properties are not just theorems but computational facts. They hold definitionally, meaning Lean can verify them by pure computation without requiring proof steps.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_api}}
```

### Function Properties

Mathematical properties of functions (injectivity, surjectivity, and bijectivity) play crucial roles in both mathematics and computer science. An injective function maps distinct inputs to distinct outputs, a surjective function reaches every possible output, and a bijective function is both injective and surjective, establishing a one-to-one correspondence between domain and codomain.

These properties connect to the concept of inverses. A function has a left inverse if and only if it's injective, a right inverse if and only if it's surjective, and a two-sided inverse if and only if it's bijective. Lean provides definitions and theorems for reasoning about these properties, enabling formal verification of mathematical and algorithmic correctness.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_properties}}
```

### Implicit and Auto Parameters

While not part of core type theory, Lean's function types include indications of whether parameters are implicit. Implicit and explicit function types are definitionally equal. Implicit parameters are inferred from context, strict implicit parameters must be inferrable at the application site, and auto parameters are filled by type class resolution.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:functions_implicit}}
```

## Propositions

Propositions (`Prop`) are types representing logical statements. They feature proof irrelevance: any two proofs of the same proposition are definitionally equal. This means the specific proof does not matter, only that one exists. We covered this in the [Type Theory](./11_type_theory.md#proof-irrelevance) article.

### The Curry-Howard Correspondence Revisited

The [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) we encountered in earlier articles now reveals its full depth. With dependent types, the correspondence extends beyond simple propositional logic. Universal quantification becomes dependent function types. Existential quantification becomes dependent pair types (sigma types). The slogan "propositions are types, proofs are programs" turns out to be a precise mathematical equivalence.

| **Logic**                      | **Type Theory**                                 | **Lean Syntax**                   |
| ------------------------------ | ----------------------------------------------- | --------------------------------- |
| $\forall x : \alpha, P(x)$ | Dependent function $\Pi (x : \alpha), P(x)$ | `∀ x : α, P x` or `(x : α) → P x` |
| $\exists x : \alpha, P(x)$ | Dependent pair $\Sigma (x : \alpha), P(x)$  | `∃ x : α, P x` or `Σ x : α, P x`  |
| Induction principle            | Recursor                                        | `Nat.rec`, `List.rec`, etc.       |
| Proof by cases                 | Pattern matching                                | `match ... with`                  |

The dependent versions unify what simpler type systems treat separately. A proof of "for all natural numbers n, P(n) holds" is literally a function that takes any `n : Nat` and returns a proof of `P n`. A proof of "there exists a natural number n such that P(n)" is literally a pair: the witness `n` together with a proof of `P n`. This unification is not philosophical hand-waving; it is the operational semantics of Lean.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:propositions_core}}
```

### Key Properties of Propositions

- **Run-time irrelevance**: Propositions are erased during compilation
- **Impredicativity**: Propositions can quantify over types from any universe
- **Restricted elimination**: With limited exceptions (subsingletons), propositions cannot eliminate to non-proposition types
- **Extensionality**: The `propext` axiom enables proving logically equivalent propositions are equal

### Decidability

Decidable propositions bridge logic and computation, allowing propositions to be computed. A proposition $P$ is decidable when we can algorithmically determine $P \lor \neg P$:

$$\text{Decidable}(P) \triangleq P \lor \neg P$$

This connects to constructive mathematics where decidability provides computational content:

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:propositions_decidable}}
```

## Universes

Lean organizes types into a hierarchy of universes to prevent paradoxes, as we discussed in the [Type Theory](./11_type_theory.md#universe-stratification) article. Every type belongs to exactly one universe level. The `Sort` operator constructs universes:

> [!TIP]
> Universe levels rarely matter in practice. Lean infers them automatically in most cases, and you can write thousands of lines of code without thinking about them. They become relevant when you are doing highly polymorphic library design or when the compiler complains about universe inconsistencies. If that happens, the error messages will guide you. Until then, treat them as plumbing that handles itself.

- $\text{Sort } 0 = \text{Prop}$ (propositions)
- $\text{Sort } (u + 1) = \text{Type } u$ (data types)
- Every universe is an element of the next larger universe: $\text{Sort } u : \text{Sort } (u + 1)$

The universe of a Pi type $\Pi (x : \alpha), \beta$ depends on the universes of $\alpha$ and $\beta$:

- If $\beta : \text{Prop}$, then $\Pi (x : \alpha), \beta : \text{Prop}$ (impredicative)
- If $\beta : \text{Sort } v$, then $\Pi (x : \alpha), \beta : \text{Sort } (\max(u, v))$ where $\alpha : \text{Sort } u$

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:universes_hierarchy}}
```

### Universe Polymorphism and Lifting

Definitions can take universe parameters, and universe levels support expressions with addition and maximum operations. Lean's universes are non-cumulative: a type in `Type u` is not automatically in `Type (u + 1)`.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:universes_lifting}}
```

Universe polymorphism lets definitions work at any universe level. The identity function, for instance, should work on values, on types, and on types of types. By parameterizing over universe levels, a single definition serves all purposes:

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:universe_polymorphism}}
```

Two operators bridge universe gaps:

- **PLift**: Lifts any type (including propositions) by exactly one level
- **ULift**: Lifts non-proposition types by any number of levels

## Inductive Types

Inductive types are Lean's primary mechanism for introducing new types. Every type is either inductive or built from universes, functions, and inductive types.

> [!WARNING]
> The recursor that Lean generates for each inductive type is the induction principle in computational form. If you find yourself writing a proof by induction and wondering where the induction hypothesis comes from, the answer is: the recursor. Understanding recursors deeply is optional for using Lean but essential for understanding why Lean works.

Each inductive type has:

- A single type constructor (may take parameters)
- Any number of constructors introducing new values
- A derived recursor representing an induction principle

The general form of an inductive type declaration:
$$\begin{aligned}
&\textbf{inductive } C (\vec{\alpha} : \vec{U}) : \Pi (\vec{\beta} : \vec{V}), s \textbf{ where} \\\\
&\quad | \, c_1 : \Pi (\vec{x_1} : \vec{T_1}), C \, \vec{\alpha} \, \vec{t_1} \\\\
&\quad | \, c_2 : \Pi (\vec{x_2} : \vec{T_2}), C \, \vec{\alpha} \, \vec{t_2} \\\\
&\quad \vdots
\end{aligned}$$

Where $\vec{\alpha}$ are parameters (fixed) and $\vec{\beta}$ are indices (can vary).

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:inductive_basic_extended}}
```

### Indexed Families

The distinction between parameters and indices is fundamental. Parameters are fixed across the entire definition: if you declare `inductive Foo (α : Type)`, then every constructor must produce a `Foo α` with that same `α`. Indices can vary: each constructor can target a different index value. In `Vector α n`, the type `α` is a parameter (all elements have the same type) but `n` is an index (constructors produce vectors of different lengths). The `nil` constructor produces `Vector α 0`. The `cons` constructor takes a `Vector α n` and produces `Vector α (n + 1)`. The index changes; the parameter does not.

This distinction affects how Lean generates recursors and what pattern matching can learn. When you match on a `Vector α n`, Lean learns the specific value of the index `n` in each branch. Matching on `nil` tells you `n = 0`. Matching on `cons` tells you `n = m + 1` for some `m`. This index refinement is what makes length-indexed vectors useful: the type system tracks information that flows from pattern matching.

For vectors (length-indexed lists), the signature is:
$$\text{Vector} : \text{Type} \to \mathbb{N} \to \text{Type}$$

The recursor for indexed families captures the dependency:
$$\text{Vector.rec} : \Pi (P : \Pi n, \text{Vector } \alpha \, n \to \text{Sort } u), \ldots$$

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:inductive_indexed}}
```

The `Fin n` type represents natural numbers strictly less than `n`. It is perhaps the simplest useful indexed type: the index constrains which values can exist. A `Fin 3` can only be 0, 1, or 2. Attempting to construct a `Fin 3` with value 3 is a type error, not a runtime error.

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:fin_basics}}
```

Vectors generalize lists by tracking their length in the type. A `Vec α n` is a list of exactly `n` elements of type `α`. The `head` function can only be called on non-empty vectors because its type requires `Vec α (n + 1)`. No runtime check needed; the type system enforces the precondition.

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:vector_type}}
```

### Mutual and Nested Inductive Types

Multiple inductive types can be defined simultaneously when they reference each other. Nested inductive types are defined recursively through other type constructors.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:inductive_mutual}}
```

### Structures

Structures are specialized single-constructor inductive types with no indices. They provide automatic projection functions, named-field syntax, update syntax, and inheritance:

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:inductive_structures}}
```

### Sigma Types and Subtypes

Sigma types (dependent pairs) package a value with data that depends on it. The notation `Σ x : α, β x` describes pairs where the second component's type depends on the first component's value. This is the dependent version of the product type `α × β`.

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:sigma_types}}
```

Subtypes refine existing types with predicates. The type `{ x : α // P x }` contains values of type `α` that satisfy predicate `P`. Each element bundles a value with a proof that it satisfies the constraint. This is how you express "positive integers" or "sorted lists" at the type level.

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:subtype}}
```

### Equality as a Type

The equality type `a = b` is itself a dependent type: it depends on the values `a` and `b`. The only constructor is `rfl : a = a`, which proves that any value equals itself. Proofs of equality can be used to substitute equal values, and equality satisfies the expected properties of symmetry and transitivity.

```lean
{{#include ../../src/ZeroToQED/DependentTypes.lean:equality_types}}
```

## Quotient Types

Quotient types create new types by identifying elements via equivalence relations. Given a type $\alpha$ and an equivalence relation $\sim$ on $\alpha$, the quotient $\alpha/\sim$ is a type where $a = b$ in $\alpha/\sim$ whenever $a \sim b$. Elements related by the relation become equal in the quotient type. Equality is respected universally, and nothing in Lean's logic can observe differences between equal terms.

> [!NOTE]
> Mathematicians write $\mathbb{Z} = (\mathbb{N} \\times \\mathbb{N})/\\!\\sim$ and software engineers write `type Int = Quotient (Nat × Nat) equiv`. Same idea, different notation. The integer $-3$ is not any particular pair of naturals but the equivalence class of all pairs $(a, b)$ where $a + 3 = b$: so $(0, 3)$, $(1, 4)$, $(2, 5)$, and infinitely many others. Two fields, one concept, a century of mutual incomprehension that turns out to be largely notational.

For example, the integers can be constructed as $\mathbb{Z} = (\mathbb{N} \times \mathbb{N})/\sim$ where $(a,b) \sim (c,d)$ iff $a + d = b + c$.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:quotient_basic}}
```

### Working with Quotients

Operations on quotients must respect the equivalence relation. The `Quotient.lift` functions ensure operations are well-defined, while `Quotient.sound` asserts equality of related elements.

The quotient axioms provide:

- **Quotient.mk**: $\alpha \to \alpha/{\sim}$ (constructor)
- **Quotient.lift**: If $f : \alpha \to \beta$ respects $\sim$, then $f$ lifts to $\alpha/{\sim} \to \beta$
- **Quotient.sound**: If $a \sim b$, then $[a] = [b]$ in $\alpha/{\sim}$
- **Quotient.exact**: If $[a] = [b]$ in $\alpha/{\sim}$, then $a \sim b$

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:quotient_operations}}
```

## Combined Examples

The following examples combine dependent functions, indexed families, and proof terms. Each demonstrates how types can enforce invariants that would be invisible to simpler type systems:

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:advanced_examples}}
```

The machinery presented here forms the foundation of everything that follows. Dependent types are why Lean can serve simultaneously as a programming language and a proof assistant. When you write a type signature like `Vector α n → Vector α (n + 1)`, you are making a mathematical claim that the compiler will verify. Specifications that the machine enforces, invariants that cannot be violated, programs that are correct by construction.

Most software is written fast, tested hopefully, and debugged frantically. Dependent types offer a different mode: slower to write, harder to learn, guarantees that survive contact with production. Whether the tradeoff makes sense depends on how much a bug costs. For most code, the answer is "not much." For some code, the answer is "careers" or "lives." Know which kind you are writing.

## From Theory to Practice

You now understand the type-theoretic machinery. The next article turns to strategy: how to approach proofs systematically, read goal states, choose tactics, and develop the intuition for what technique applies where. Less "what does this mean" and more "how do I make this red squiggle go away."
