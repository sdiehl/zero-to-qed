# Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) is the mathematical library for Lean 4. It contains over a million lines of formalized mathematics, from basic logic through graduate-level algebra, analysis, and number theory. When you import Mathlib in your project, you gain access to thousands of theorems, definitions, and tactics developed by hundreds of contributors. Understanding its structure helps you find what you need and write code that integrates cleanly with the ecosystem.

The library is organized hierarchically. At the foundation sit logic, sets, and basic data types. Above these rise algebraic structures, then topology and analysis, then specialized domains like combinatorics and number theory. Each layer builds on those below. The [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) provides searchable API references for every module.

## Core Foundations

These modules provide the logical and set-theoretic foundations that everything else depends on.

| Module | Description |
|:-------|:------------|
| [`Mathlib.Logic.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html) | Core logical connectives, `And`, `Or`, `Not`, `Iff`, basic lemmas |
| [`Mathlib.Init.Classical`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Classical.html) | Classical axioms: `Classical.em`, `Classical.choose`, `Classical.byContradiction` |
| [`Mathlib.Data.Set.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html) | Set operations: union, intersection, complement, membership |
| [`Mathlib.Data.Finset.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html) | Finite sets with decidable membership |
| [`Mathlib.Order.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Basic.html) | Partial orders, lattices, suprema and infima |

## Algebraic Hierarchy

Mathlib builds algebra through a hierarchy of type classes. Each structure adds operations and axioms to those below it.

| Module | Description |
|:-------|:------------|
| [`Mathlib.Algebra.Group.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Basic.html) | Monoids, groups, abelian groups |
| [`Mathlib.Algebra.Ring.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Basic.html) | Semirings, rings, commutative rings |
| [`Mathlib.Algebra.Field.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Basic.html) | Division rings, fields |
| [`Mathlib.Algebra.Module.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Basic.html) | Modules over rings, vector spaces |
| [`Mathlib.LinearAlgebra.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basic.html) | Linear maps, submodules, quotients |
| [`Mathlib.RingTheory.Ideal.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Basic.html) | Ideals, quotient rings |

## Number Systems

The standard number types and their properties.

| Module | Description |
|:-------|:------------|
| [`Mathlib.Data.Nat.Prime.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Basic.html) | Prime numbers, factorization |
| [`Mathlib.Data.Int.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Int/Basic.html) | Integers |
| [`Mathlib.Data.Rat.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Rat/Basic.html) | Rational numbers |
| [`Mathlib.Data.Real.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html) | Real numbers (Cauchy completion) |
| [`Mathlib.Data.Complex.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html) | Complex numbers |
| [`Mathlib.Data.ZMod.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html) | Integers modulo n |

## Analysis and Topology

Continuous mathematics built on topological foundations.

| Module | Description |
|:-------|:------------|
| [`Mathlib.Topology.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Basic.html) | Topological spaces, open sets, continuity |
| [`Mathlib.Topology.MetricSpace.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Basic.html) | Metric spaces, distances |
| [`Mathlib.Analysis.Normed.Field.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Field/Basic.html) | Normed fields |
| [`Mathlib.Analysis.Calculus.Deriv.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Basic.html) | Derivatives |
| [`Mathlib.MeasureTheory.Measure.MeasureSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpace.html) | Measure spaces, integration |

## Category Theory and Combinatorics

Abstract structures and discrete mathematics.

| Module | Description |
|:-------|:------------|
| [`Mathlib.CategoryTheory.Category.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html) | Categories, functors, natural transformations |
| [`Mathlib.CategoryTheory.Limits.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Basic.html) | Limits and colimits |
| [`Mathlib.CategoryTheory.Monad.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monad/Basic.html) | Monads in category theory |
| [`Mathlib.Combinatorics.SimpleGraph.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html) | Graph theory |
| [`Mathlib.Combinatorics.Pigeonhole`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Pigeonhole.html) | Pigeonhole principle |

## Finding What You Need

Mathlib is large. These strategies help you navigate it.

**In-editor search**: The `exact?` tactic searches for lemmas that exactly match your goal. The `apply?` tactic finds lemmas whose conclusion unifies with your goal.

**Pattern search**: [Loogle](https://loogle.lean-lang.org/) searches Mathlib by type signature. If you need a lemma about `List.map` and `List.length`, search for `List.map, List.length` and find `List.length_map`.

**Natural language search**: [Moogle](https://www.moogle.ai/) uses semantic search to find lemmas from natural language queries. Ask "triangle inequality for norms" and find `norm_add_le`.

**Naming conventions**: Mathlib follows predictable naming. A lemma about `add` and `comm` is likely named `add_comm`. A lemma about `mul`, `zero`, and the left side is `mul_zero` or `zero_mul`. Once you internalize the pattern, you can often guess lemma names.

**Module structure**: If you need facts about prime numbers, look in `Mathlib.Data.Nat.Prime`. If you need topology lemmas, start in `Mathlib.Topology`. The [Mathematics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html) overview provides a comprehensive map of what is formalized and where to find it.

## Importing Mathlib

Most projects import Mathlib wholesale:

```lean
import Mathlib
```

For faster compilation during development, import only what you need:

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
```

The [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) lists all available modules. When your proof needs a specific lemma, check which module provides it and add that import.
