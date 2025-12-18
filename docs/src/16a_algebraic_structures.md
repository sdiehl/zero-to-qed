# Algebraic Structures

Mathematics organizes operations into hierarchies. A group is not just a set with an operation; it is a semigroup with identity and inverses, and a semigroup is a set with an associative operation. These hierarchies matter because theorems proved at one level apply to all structures below it. Prove something about groups, and it holds for integers, permutations, and matrix transformations alike.

Lean captures these hierarchies through type classes. Each algebraic structure becomes a type class, and instances register specific types as members. The type class system then automatically provides the right theorems and operations wherever they apply. The notation is convenient, but the real value is the machinery underneath: generic mathematical code that works across any conforming type.

## Semigroups

A semigroup is the simplest algebraic structure: a type with a binary operation that is associative. Nothing more. No identity element, no inverses, just the guarantee that \\((a \cdot b) \cdot c = a \cdot (b \cdot c)\\).

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:semigroup}}
```

The `op_assoc` field is a proof that clients can use directly. Any theorem about semigroups can invoke this associativity without asking whether a particular type satisfies it. The type class instance guarantees it.

## Monoids

A monoid extends a semigroup with an identity element. The identity must satisfy two laws: left identity (\\(e \cdot a = a\\)) and right identity (\\(a \cdot e = a\\)). Natural numbers under addition form a monoid with identity 0. Natural numbers under multiplication form a different monoid with identity 1. Same type, different structures.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:monoid}}
```

The `extends Semigroup α` clause means every monoid is automatically a semigroup. Lean's type class inheritance handles this: any function expecting a semigroup accepts a monoid. The hierarchy is operational, not merely conceptual.

## Groups

A group adds inverses to a monoid. Every element \\(a\\) has an inverse \\(a^{-1}\\) such that \\(a^{-1} \cdot a = e\\) and \\(a \cdot a^{-1} = e\\). Integers under addition form a group. Positive rationals under multiplication form a group. Permutations under composition form a group. The examples proliferate across mathematics.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:group_def}}
```

With this definition, we can prove fundamental group theorems that apply to any group. These are not approximations or heuristics; they are mathematical facts verified by the type checker.

## Group Theorems

From just the group axioms, many properties follow. Cancellation laws let us simplify equations. The identity is unique, as are inverses. The inverse of a product reverses the order. These theorems are mechanical consequences of the axioms, and Lean verifies each step.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:group_theorems}}
```

The theorem `op_inv_rev` shows that \\((a \cdot b)^{-1} = b^{-1} \cdot a^{-1}\\). The order reverses because we need to undo the operations in reverse sequence. The proof uses our `inv_unique` theorem: to show two things are equal to an inverse, show they act as that inverse.

## A Concrete Example: Integers Mod 2

Theory without examples is suspect. Let us build a concrete group: integers modulo 2. This group has exactly two elements (zero and one) with addition wrapping around: \\(1 + 1 = 0\\).

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:int2_def}}
```

Every element is its own inverse (\\(0 + 0 = 0\\) and \\(1 + 1 = 0\\)), which simplifies the structure. Now we register this as a group instance:

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:int2_group}}
```

Each proof obligation is discharged by case analysis. With only two elements, Lean can verify each law by exhaustively checking all combinations.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:int2_theorems}}
```

Because `Z2` is now a `Group`, all our general theorems apply. The `op_left_cancel` and `inv_unique` theorems work on `Z2` without modification. Generic mathematics, specific verification.

## Commutative Groups

Some groups satisfy an additional property: commutativity. In a commutative (or Abelian) group, \\(a \cdot b = b \cdot a\\) for all elements. Integer addition is commutative; matrix multiplication is not.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:comm_group}}
```

## Vector Spaces

Groups appear everywhere, including in linear algebra. A vector space is an Abelian group (vectors under addition) equipped with scalar multiplication satisfying certain compatibility laws. Let us build a simple 2D vector space over the integers.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:vector_space_def}}
```

The vectors form a group under addition. Each vector \\((x, y)\\) has inverse \\((-x, -y)\\), and the zero vector is the identity.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:vector_space_group}}
```

Scalar multiplication satisfies the expected laws. These are the axioms that make scalar multiplication "compatible" with the vector space structure.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:vector_space_theorems}}
```

Concrete computations confirm the definitions work:

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:vector_examples}}
```

## Rings

A ring has two operations: addition forming an Abelian group, and multiplication forming a monoid. Distributivity connects them: \\(a \cdot (b + c) = a \cdot b + a \cdot c\\). Integers, polynomials, and matrices all form rings.

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:ring_def}}
```

The integers satisfy all ring axioms:

```lean
{{#include ../../src/ZeroToQED/AlgebraicStructures.lean:integers_ring}}
```

From these axioms, one can prove that \\(0 \cdot a = 0\\) for any ring element \\(a\\). This follows from distributivity: \\(0 \cdot a + 0 \cdot a = (0 + 0) \cdot a = 0 \cdot a\\), and cancellation gives \\(0 \cdot a = 0\\). See `ring_zero_mul` and `ring_mul_zero` in [AlgebraicStructures.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/AlgebraicStructures.lean) for the full proofs.

## The Hierarchy

The structures we have defined form a hierarchy. At the base sits **Semigroup**, requiring only an associative operation. **Monoid** extends Semigroup by adding an identity element. **Group** extends Monoid by adding inverses. From Group, two paths diverge: **CommGroup** adds commutativity, while **Ring** combines an abelian group (for addition) with a monoid (for multiplication) linked by distributivity.

Each extension relationship means theorems flow downward. Prove something about semigroups, and it applies to monoids, groups, and rings. Lean's type class inheritance makes this operational: any function expecting a Semigroup instance automatically accepts a Monoid, Group, or Ring.

Mathlib takes this much further. The full algebraic hierarchy includes semirings, division rings, fields, modules, algebras, and dozens of ordered variants. Each structure captures a precise set of assumptions, and theorems are proved at exactly the level of generality where they hold.

## From First Principles to Mathlib

We built these structures from scratch to understand how they work. In practice, you would use Mathlib's definitions, which are battle-tested and integrated with thousands of theorems. Our `Group` is Mathlib's `Group`. Our `MyRing` is Mathlib's `Ring`. The concepts are identical; the implementations are industrial-strength.

The value of building from first principles is understanding. When Mathlib's `ring` tactic solves a polynomial identity, it is applying theorems like our `ring_zero_mul` millions of times per second. When type class inference finds a `CommGroup` instance, it is navigating a hierarchy like the one we drew. The abstraction is real, and so is the machinery underneath.
