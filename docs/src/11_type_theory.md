# Type Theory

Humans classify. We sort animals into species, books into genres, people into roles, and programmers into those who have mass-assigned `any` to silence the compiler and those who are lying about it. Classification is how finite minds manage infinite variety. Types are classification for computation: every value belongs to a type, and the type determines what operations make sense. You can add numbers but not strings. You can take the length of a list but not the length of an integer. The type system enforces these distinctions before your program runs, which sounds obvious until you remember that most of the world's software runs on languages where the type system's considered opinion is "looks plausible" right up until production catches fire.

This seems pedestrian until you push it. What if types could say not just "this is a list" but "this is a list of exactly five elements"? What if they could say not just "this function returns an integer" but "this function returns a positive integer"? What if the type of a function could express its complete specification, so that any implementation with that type is correct by construction?

Dependent type theory answers yes to all of these. It is the most expressive type system in common use, and it blurs the line between programming and mathematics. A type becomes a proposition. A program becomes a proof. The compiler becomes a theorem checker. This is not metaphor; it is the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) that we met in the previous article, now unleashed to its full power.

## The Ladder of Expressiveness

Type systems form a ladder. Each rung lets you say more.

**Simple types** (C, Java): Values have types. `int`, `string`, `bool`. You cannot add a string to an integer. This catches typos and category errors, but nothing deeper.

**Polymorphic types** (Haskell, OCaml): Types can be parameterized. `List α` works for any element type. You write one `reverse` function that works on lists of integers, strings, or custom objects. The type `∀ α. List α → List α` says "for any type α, give me a list of α and I'll return a list of α."

**Dependent types** (Lean, Coq, Agda): Types can depend on values. `Vector α n` is a list of exactly `n` elements. The number `n` is a value that appears in the type. Now the type system can express array bounds, matrix dimensions, protocol states, and any property you can state precisely.

The jump from polymorphic to dependent types is where things get interesting. Consider matrix multiplication. Two matrices can only be multiplied if the columns of the first equal the rows of the second. With dependent types:

```
Matrix m n → Matrix n p → Matrix m p
```

The shared `n` enforces compatibility at compile time. Multiply a 3×4 by a 5×2? Type error. The bug is caught before any code runs. Your linear algebra homework now has compile errors, which is somehow both better and worse.

## Types as First-Class Citizens

In simple type systems, types and values live in separate worlds. You cannot write a function that takes a type as an argument or returns a type as a result. The wall between them is absolute.

Dependent types tear down this wall. Types become values. You can compute with them, pass them to functions, store them in data structures. The function that constructs `Vector Int n` takes a number `n` and returns a type. This uniformity is what makes the whole system work: if types can depend on values, then types must be values.

The theoretical foundations trace through the 20th century: [Russell](https://en.wikipedia.org/wiki/Bertrand_Russell)'s type distinctions to resolve paradoxes, [Church](https://en.wikipedia.org/wiki/Alonzo_Church)'s simply typed lambda calculus, [Martin-Löf](https://en.wikipedia.org/wiki/Per_Martin-L%C3%B6f)'s intuitionistic type theory that unified logic and computation. Lean implements a refinement called the [Calculus of Inductive Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions), which adds inductive types and a hierarchy of universes to keep everything consistent.

The practical experience differs from conventional programming. Types become more informative but also more demanding. You must often provide proofs alongside your code, demonstrating that values satisfy required properties. The compiler becomes an adversary that checks your reasoning at every step, as we saw with tactics. When a program type-checks, you gain strong guarantees about its behavior. When it fails, the error messages guide you toward the gap between what you claimed and what you proved.

## Universes and Russell's Paradox

When you write `universe u v w` in Lean, you are declaring universe level variables. If that sentence meant nothing to you, good. It should not mean anything yet. But why do universes exist at all? The answer involves one of the most famous disasters in the history of mathematics, a polite letter that ended a career, and the dawning realization that self-reference is the serpent in every formal garden.

In 1901, [Bertrand Russell](https://en.wikipedia.org/wiki/Russell%27s_paradox) sent a letter to Gottlob Frege, who had just completed his life's work: a logical foundation for all of mathematics. Russell's letter contained a single question. Consider the set R of all sets that do not contain themselves. Does R contain itself? If yes, then by definition it should not. If no, then by definition it should. Frege's system was inconsistent. His life's work collapsed. He wrote back: "Hardly anything more unfortunate can befall a scientific writer than to have one of the foundations of his edifice shaken after the work is finished."

This is the danger of self-reference. A set that asks about its own membership. A sentence that asserts its own falsehood. A type that contains itself. These constructions look innocent but harbor contradictions. Mathematics needed walls to prevent them.

Type theory builds those walls through stratification. Types are organized into a hierarchy of universes. In Lean, `Prop` sits at `Sort 0`, `Type 0` sits at `Sort 1`, `Type 1` sits at `Sort 2`, and so on. A type at level n can only mention types at levels below n. The type `Type 0` itself has type `Type 1`, not `Type 0`. This breaks the self-reference. You cannot ask whether `Type` contains itself because `Type` is not a single thing; it is an infinite ladder, and each rung can only see the rungs below.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:universes_hierarchy}}
```

The declaration `universe u v w` introduces universe level variables. When you write `def polyIdentity (α : Sort u) (a : α) : α := a`, you are defining a function that works at any universe level. The `Sort u` includes both `Prop` (when u = 0) and `Type n` (when u = n + 1). Universe polymorphism lets you write single definitions that work across the entire hierarchy.

### Predicativity and Impredicativity

Here is a rule that sounds obvious until you think about it: you cannot be in the photograph you are taking. The photographer stands outside the frame. A committee that selects its own members creates paradoxes of legitimacy. A definition that refers to a collection containing itself is suspect. This intuition, that the definer must stand apart from the defined, is called predicativity.

Imagine a monastery where knowledge is organized into concentric walls. Acolytes in the outer ring may study only texts from their own ring. Scholars who wish to reference the entire outer collection must do so from the second ring, looking inward. Those who would survey the second ring must stand in the third. And so on, each level permitted to see only what lies below. No scholar may cite a collection that includes their own work. The hierarchy prevents the serpent from eating its tail.

This is how predicative universes work. When you quantify over all types at level n, the resulting type lives at level n+1. The definition "for all types α in `Type 0`, the type `α → α`" must itself live in `Type 1` because it speaks about the entirety of `Type 0`. You cannot make universal claims about a collection while remaining inside it. The quantification must ascend.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:predicativity}}
```

Lean's `Type` hierarchy is predicative: `∀ (α : Type 0), α → α` has type `Type 1`, not `Type 0`. This prevents [Girard's paradox](https://en.wikipedia.org/wiki/System_U#Girard's_paradox), a type-theoretic ouroboros that arises when `Type : Type`. The infinite regress of universes is the price of consistency.

But `Prop` breaks the rule. Lean's `Prop` is impredicative: `∀ (P : Prop), P → P` has type `Prop`, staying at the same level despite quantifying over all propositions. The monastery has a secret inner sanctum where the old restrictions do not apply. How is this safe?

Proof irrelevance is the answer. In `Prop`, all proofs of the same proposition are equal. You cannot extract computational content from an impredicative definition over propositions because there is nothing to extract; all witnesses are indistinguishable. The dangerous circularity is defanged. The serpent may eat its tail here because the tail has no substance.

This matters for classical logic. The law of excluded middle, `∀ (P : Prop), P ∨ ¬P`, quantifies over all propositions. If `Prop` were predicative, this would live in `Type 0`, making it a computational object rather than a logical axiom. The monks in the inner sanctum can do things forbidden to those outside because what happens in `Prop` stays in `Prop`. The walls are there to protect computation from paradox; proof lives by different rules.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:universes_lifting}}
```

### Non-Cumulativity {#non-cumulativity}

In a cumulative type theory, every type at universe level n is automatically also a type at level n+1 and all higher levels. Coq and Idris work this way: if you have `Nat : Type 0`, you can use `Nat` anywhere a `Type 1` is expected. The type "flows upward" through the hierarchy without explicit intervention. This makes polymorphic code more convenient since you rarely need to think about universe levels.

Lean takes the opposite approach. Each type lives at exactly one universe level. `Nat` has type `Type 0` and only `Type 0`. If a function expects a `Type 1` argument, you cannot pass `Nat` directly. You must explicitly lift it using `ULift` or `PLift`, wrapper types that move values to higher universes.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:non_cumulativity}}
```

> [!NOTE]
> This explicit lifting makes universe structure visible in your code. You always know exactly which universe level you are working at. The tradeoff is verbosity: code that would "just work" in Coq requires explicit lifts in Lean. In practice, most Lean code stays within `Type 0` and `Prop`, so non-cumulativity rarely causes friction.

## Proof Irrelevance

A bear catching a salmon does not care whether the fish swam upstream via the left channel or the right. Philosophers have spent centuries on equivalent questions about identity and equivalence, producing volumes that the bear would find unpersuasive. Proof irrelevance applies this principle to mathematics: any two proofs of the same proposition are equal. If you have two proofs `p1` and `p2` that both establish proposition `P`, then `p1 = p2` holds definitionally. We care that the theorem is true, not which path led there. This is either profound or obvious depending on how much time you've spent arguing about equality, which is to say, depending on whether you've ever debugged a language with more than three equality operators.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:propositions_core}}
```

Proof irrelevance has profound computational implications. Because all proofs of a proposition are equal, the compiler can erase proofs at runtime. A function that takes a proof argument does not actually need to receive any runtime data for that argument. This erasure is essential for performance: without it, complex proofs would bloat compiled code with useless proof terms. Your elaborate justification for why the code is correct compiles down to nothing, much like comments but with mathematical guarantees.

The technical foundation is that `Prop` is a subsingleton universe. A subsingleton is a type with at most one element. For any proposition P, there is at most one proof of P up to definitional equality. This contrasts with `Type`, where `Bool` has two distinct elements `true` and `false`, and `Nat` has infinitely many.

Proof irrelevance also enables powerful automation. When a tactic constructs a proof term, the exact structure of that term does not matter. The tactic can use whatever construction is convenient, and the result will be equal to any other proof of the same statement. This freedom simplifies tactic implementation and allows for aggressive optimization of proof search.

## Constructive and Classical Logic

Lean's type theory is constructive at its core. A constructive proof of existence must provide a witness: to prove `∃ n, P n`, you must exhibit a specific `n` and show `P n` holds. You cannot merely argue that non-existence leads to contradiction. This discipline has a profound consequence: constructive proofs are programs. A proof of `∃ n, n * n = 4` contains the number 2. You can extract it and compute with it.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:constructive_classical}}
```

Classical logic adds axioms that break this computational interpretation. The law of excluded middle (`P ∨ ¬P` for any proposition) lets you prove existence by contradiction without producing a witness. Double negation elimination (`¬¬P → P`) lets you escape a double negation without constructing a direct proof. These principles are mathematically sound but computationally empty. When you prove something exists using excluded middle, the proof does not contain the thing that exists.

Lean provides classical axioms through the `Classical` namespace. When you use `Classical.em` or tactics like `by_contra`, you are stepping outside constructive logic. Lean tracks this: definitions that depend on classical axioms are marked `noncomputable`, meaning they cannot be evaluated at runtime.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:noncomputable_examples}}
```

Why does this matter? For pure mathematics, classical reasoning is often more convenient. Many standard proofs use contradiction freely. But for verified programming, constructive proofs have an advantage: they produce code. A constructive proof that a sorting algorithm returns a sorted list can be extracted into an actual sorting function. A classical proof merely asserts the sorted list exists.

The practical guidance: use constructive methods when you can, classical when you must. Lean supports both. When you see `noncomputable` on a definition, you know it relies on classical axioms and cannot be executed. When a definition lacks that marker, it is constructive and can run. The type system tracks the distinction so you always know which world you are in.

## Quotients and Parametricity

Quotient types allow you to define new types by identifying elements of an existing type according to an equivalence relation. The integers modulo n, for example, identify natural numbers that have the same remainder when divided by n. Quotients are essential for constructing mathematical objects like rational numbers, real numbers, and algebraic structures.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:quotient_basic}}
```

However, quotients break parametricity. Parametricity is the principle that polymorphic functions must treat their type arguments uniformly. A function of type `∀ α, α → α` can only be the identity function because it has no way to inspect what α is. It must work the same way for `Nat`, `String`, and any other type. This uniformity yields powerful "free theorems" about polymorphic functions.

Quotients violate this uniformity through the `Quot.lift` operation. When you lift a function to operate on a quotient type, you must prove that the function respects the equivalence relation. This proof obligation means that functions on quotients can behave differently depending on the specific equivalence relation, breaking the uniformity that parametricity requires.

```lean
{{#include ../../src/ZeroToQED/TypeTheory.lean:quotient_operations}}
```

Why is this acceptable? The trade-off is deliberate. Quotients are necessary for mathematics: you cannot construct the integers, rationals, or reals without them. The loss of parametricity is confined to quotient types and does not affect ordinary polymorphic functions. Moreover, the requirement to prove that lifted functions respect equivalence ensures that quotient operations are well-defined. You cannot accidentally distinguish between equivalent elements.

## Comparative Type Systems

Different languages make different design choices in their type systems. The following table summarizes key features across proof assistants and programming languages.

| Feature | Lean 4 | Coq | Agda | Idris 2 | Haskell | Rust |
|:--------|:------:|:---:|:----:|:-------:|:-------:|:----:|
| **Dependent Types** | Full | Full | Full | Full | Limited | No |
| **Universe Hierarchy** | Predicative | Predicative | Predicative | Predicative | None | None |
| **[Universe Cumulativity](#non-cumulativity)** | No | Yes | No | Yes | N/A | N/A |
| **[Proof Irrelevance](#proof-irrelevance)** | Yes (Prop) | Yes (Prop) | Optional | Yes | N/A | N/A |
| **Tactic Language** | Lean DSL | Ltac | No | Elab | N/A | N/A |
| **Type Inference** | Partial | Partial | Partial | Partial | Sorta Full | Full |
| **Termination Checking** | Required | Required | Required | Optional | No | No |
| **Linear Types** | No | No | No | QTT | Extension | Ownership |
| **Effects System** | Monad | Monad | Monad | Algebraic | Monad | Ownership |
| **Code Generation** | Native | OCaml/Haskell | Haskell | Native | Native | Native |
| **Cubical Type Theory** | No | No | Yes | No | No | No |
| **Decidable Type Checking** | No | No | No | No | Sorta | Yes |

**Glossary**:
- **Ltac**: Coq's original tactic language, a dynamically-typed scripting language for proof automation
- **QTT**: Quantitative Type Theory, tracks how many times each variable is used to enable linear resource management
- **[Predicative](#predicativity-and-impredicativity)**: A universe is predicative if quantifying over types at level n produces a type at level n+1 or higher
- **[Cumulativity](#non-cumulativity)**: Whether a type at level n is automatically also at level n+1
- **Sorta Full**: Haskell has full type inference for base Haskell 2010, but enabling type system extensions (GADTs, TypeFamilies, RankNTypes, etc.) may require type annotations
- **Sorta** (Decidable): Haskell 2010 has decidable type checking, but extensions like UndecidableInstances and TypeFamilies can make type checking undecidable or non-terminating

Lean and Coq provide full dependent types with rich proof automation, making them suitable for formal verification. Agda emphasizes explicit proof terms and supports cubical type theory for constructive equality. Idris 2 uses quantitative type theory to track resource usage, bridging the gap between theorem proving and systems programming.

Haskell approaches dependent types through extensions like GADTs, DataKinds, and type families. Base Haskell maintains decidable type checking, but common extensions can introduce undecidability. Rust's ownership system provides memory safety guarantees through affine types, with decidable checking and predictable compile times.

A common critique of Lean is its lack of linear or affine types, which would enable compile-time guarantees about resource usage and in-place mutation. The Lean developers chose instead to rely on runtime reference counting with FBIP optimizations, trading static linearity guarantees for simpler types and the ability to share data freely without borrow checker complexity.

The table above looks like a feature comparison. It is actually a map of philosophical commitments. Each row is a question about the nature of computation; each column is an answer. The language you choose chooses what thoughts are easy to think.

The fundamental trade-off is expressiveness versus automation. Full dependent types let you express arbitrary properties but require manual proof effort. Decidable type systems like Rust and Haskell infer types automatically but cannot express many important invariants. Choose based on whether you need machine-checked proofs or just strong static guarantees.

In short: Lean and Coq make you prove everything is correct, Rust makes you prove memory is safe, Haskell makes you prove effects are tracked, and most other languages just trust you not to ship on Friday.

## Where Types Meet Values

Type theory provides the foundation. The next chapter explores dependent types in depth: how types can depend on values, how propositions become types, and how proofs become programs. This is where Lean's power as a theorem prover emerges from its foundations as a programming language.
