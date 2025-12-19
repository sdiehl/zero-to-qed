# Congruence and Subtyping

Every type system makes tradeoffs between precision and convenience. A function that takes `Nat` will accept any natural number, including zero, even when zero would cause a division error three stack frames later. A function that takes `Int` cannot directly accept a `Nat` without explicit conversion, even though every natural number is an integer. The constraints are either too loose or the syntax is too verbose. Pick your frustration.

Lean provides tools to fix both problems. Subtypes let you carve out precisely the values you want: positive numbers, non-empty lists, valid indices. The constraint travels with the value, enforced by the type system. Coercions let the compiler insert safe conversions automatically, so you can pass a `Nat` where an `Int` is expected without ceremony. These mechanisms together give you precise types with ergonomic syntax.

Types are sets with attitude. A `Nat` carries the natural numbers along with all their operations and laws. A subtype narrows this: the positive natural numbers are the naturals with an extra constraint, a proof obligation that travels with every value. This is refinement: taking a broad type and carving out the subset you actually need.

The other direction is coercion. When Lean expects an `Int` but you give it a `Nat`, something must convert between them. Explicit casts are tedious. Coercions make the compiler do the work, inserting conversions automatically where safe. The result is code that looks like it mixes types freely but maintains type safety underneath.

Congruence handles the third concern: propagating equality. If `a = b`, then `f a = f b`. This seems obvious, but the compiler needs to be told. The `congr` tactic applies this principle systematically, breaking equality goals into their components.

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

`CoeFun` coerces values to functions, allowing structures to behave like callable objects.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:coe_sort}}
```

## Congruence

The `congr` tactic applies congruence reasoning: if you need to prove `f a = f b` and you know `a = b`, congruence can close the goal.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:congruence_basic}}
```

## Congruence with Multiple Arguments

Congruence works with functions of multiple arguments, generating subgoals for each argument that differs.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:congruence_args}}
```

## Substitution and Rewriting

The `subst` tactic substitutes equal terms, and `rw` rewrites using equalities. These are fundamental tactics for equality reasoning.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:subst_rewrite}}
```

## Type Conversion

Lean provides automatic coercion between numeric types and explicit conversion functions.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:cast_convert}}
```

## Decidable Propositions

A proposition is decidable if there is an algorithm to determine its truth. This enables using propositions in if-expressions.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:decidable_prop}}
```

## Type Class Inheritance

Type classes can extend other classes, creating inheritance hierarchies. A type implementing a subclass automatically implements its parent classes.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:type_class_subtyping}}
```

## Universe Polymorphism

Types live in a hierarchy of universes. `Type` is shorthand for `Type 0`, and each type has a type in the next universe.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:universe_subtyping}}
```

## Structure Extension

Structures can extend other structures, inheriting their fields while adding new ones.

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:structure_extension}}
```

## Nominal vs Structural Typing

Lean uses [nominal typing](https://en.wikipedia.org/wiki/Nominal_type_system): two types with identical structures are still distinct types. This prevents accidental mixing of values with different semantics. A `UserId` and a `ProductId` might both be integers underneath, but you cannot accidentally pass one where the other is expected. The bug where you deleted user 47 because product 47 was out of stock becomes a compile error. Nominal typing is the formal version of "label your variables."

```lean
{{#include ../../src/ZeroToQED/Subtyping.lean:nominal_structural}}
```

## Classic Results

The machinery is in place. You understand types, proofs, tactics, and the refinements that make specifications precise. Next we put it all together: classic mathematical proofs formalized in Lean. Bezout's identity, the infinitude of primes, the irrationality of root two. All the greatest hits.
