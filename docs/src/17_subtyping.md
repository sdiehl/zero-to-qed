# Subtypes and Coercions

Every type system makes tradeoffs between precision and convenience. A function that takes `Nat` will accept any natural number, including zero, even when zero would cause a division error three stack frames later. A function that takes `Int` cannot directly accept a `Nat` without explicit conversion, even though every natural number is an integer. The constraints are either too loose or the syntax is too verbose. Pick your frustration.

Lean provides tools to fix both problems. **Subtypes** let you carve out precisely the values you want: positive numbers, non-empty lists, valid indices. The constraint travels with the value, enforced by the type system. **Coercions** let the compiler insert safe conversions automatically, so you can pass a `Nat` where an `Int` is expected without ceremony. These mechanisms together give you precise types with ergonomic syntax.

Types are sets with attitude. A `Nat` carries the natural numbers along with all their operations and laws. A subtype narrows this: the positive natural numbers are the naturals with an extra constraint, a proof obligation that travels with every value. This is refinement: taking a broad type and carving out the subset you actually need.

The other direction is coercion. When Lean expects an `Int` but you give it a `Nat`, something must convert between them. Explicit casts are tedious. Coercions make the compiler do the work, inserting conversions automatically where safe. The result is code that looks like it mixes types freely but maintains type safety underneath.

A word about the title. Neither mechanism is **subtyping** in the sense familiar from Java, TypeScript, or OCaml's object system. Those languages have a subsumption rule: if `S` is a subtype of `T`, a value of type `S` can be used wherever a `T` is expected, with no change to the value and no change to the term. Lean's type theory has no such rule. A `Positive` is not a `Nat`; it is a pair of a `Nat` and a proof, and using it as a `Nat` means projecting out the first component. A `Nat` is not an `Int`; using it as one means the elaborator quietly inserted a call to `Int.ofNat`. In both cases the conversion is a real function application that you can print and reason about. The [Lean reference manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/) describes `Subtype` as a structure, which is exactly what it is. Keep this in mind and the behavior of both features stops being surprising.

## Subtypes

A subtype refines an existing type with a predicate. Values of a subtype carry both the data and a proof that the predicate holds.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:subtype_definition}}
```

## Working with Subtypes

Functions on subtypes can access the underlying value and use the proof to ensure operations are safe.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:subtype_operations}}
```

## Refinement Types

Subtypes let you express precise invariants. Common patterns include bounded numbers, non-zero values, and values satisfying specific properties.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:refinement_types}}
```

## Basic Coercions

Coercions allow automatic type conversion. When a value of type A is expected but you provide type B, Lean looks for a coercion from B to A.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:coercion_basic}}
```

## Coercion Chains

Coercions can chain together. If there is a coercion from A to B and from B to C, Lean can automatically convert from A to C.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:coercion_chain}}
```

## Function Coercions

`CoeFun` allows values to be used as functions. This is useful for callable objects and function-like structures.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:coercion_function}}
```

## Sort Coercions

`CoeSort` coerces values to types, so a structure that bundles a carrier type (a group, a graph, a category) can be written where a type is expected: `x : G` instead of `x : G.carrier`.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:coe_sort}}
```

## What Coercions Are Not

Because coercions are inserted silently, it is tempting to read `n : Int` for a natural `n` as evidence that `Nat` is a subtype of `Int`. It is not. The elaborator saw a `Nat` where an `Int` was expected, searched for a `Coe Nat Int` instance, and rewrote the term to `↑n`, which unfolds to `Int.ofNat n`. Hovering over the arrow in the editor shows the inserted function. The consequences are practical. A `List Nat` does not coerce to a `List Int`, because no instance says it should, and the elaborator will not invent one by mapping over the list. A function `Nat → Nat` is not a `Nat → Int`. And an equation `(↑n : Int) = ↑m` does not reduce to `n = m` by itself; a lemma such as `Int.ofNat_inj` has to do it. The same holds for subtypes in the other direction: a `Positive` becomes a `Nat` only through `.val`. Lean does ship a `CoeOut` instance that inserts that projection, but it fires only when the elaborator can see the `Subtype` underneath, so `(five : Nat)` elaborates if `Positive` is declared with `abbrev` and fails if it is declared with `def`. Even then `five + 1` is rejected, because `HAdd Positive Nat ?` has no instance and the coercion is never tried on the operands of `+`.

The upside of this honesty is that every conversion is a term, and terms have lemmas. Mathlib's `norm_cast` and `push_cast` tactics exist precisely to move the arrows around, and the `simp` set knows that `((n + m : Nat) : Int) = (n : Int) + (m : Int)`. In a language with true subsumption there would be nothing to prove and also nothing to compute with.

## Type Conversion

Lean provides automatic coercion between numeric types and explicit conversion functions.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:cast_convert}}
```

## Decidable Propositions

A proposition is **decidable** if there is an algorithm to determine its truth. This enables using propositions in if-expressions.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:decidable_prop}}
```

## Nominal vs Structural Typing

Lean uses [nominal typing](https://en.wikipedia.org/wiki/Nominal_type_system): two types with identical structures are still distinct types. This prevents accidental mixing of values with different semantics. A `UserId` and a `ProductId` might both be integers underneath, but you cannot accidentally pass one where the other is expected. The bug where you deleted user 47 because product 47 was out of stock becomes a compile error. Nominal typing is the formal version of "label your variables."

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:nominal_structural}}
```

## Into the Library

Subtypes carry proofs with values. Coercions let the elaborator convert between types for you. Together they make specifications precise without making every line a cast. The next article turns to Mathlib, the library where these mechanisms are used at scale: `↑` appears in nearly every statement that mixes number systems, and subtypes underlie everything from `Fin n` to the positive reals. Learning to find, import, and use what is already proven is the last skill you need before the classic proofs.
