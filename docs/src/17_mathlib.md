# Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) is the mathematical library for Lean 4. Over a million lines of formalized mathematics, from basic logic through graduate-level algebra, analysis, and number theory. Hundreds of contributors have poured years of work into this thing. When you import it, you inherit their labor. The triangle inequality is already proven. So is the fundamental theorem of algebra. You do not need to prove that primes are infinite; someone did that in 2017 and you can just use it. The community tracks progress against a list of [100 major theorems](https://leanprover-community.github.io/100.html); most are done.

The library is organized hierarchically, which is a polite way of saying "good luck finding anything without help." At the foundation sit logic, sets, and basic data types. Above these rise algebraic structures, then topology and analysis, then specialized domains like combinatorics and number theory. Each layer builds on those below. The [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) provides searchable API references, though "searchable" is doing some heavy lifting in that sentence.

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

Mathlib is large. You will spend more time searching for lemmas than proving theorems, at least at first. Accept this. The good news is that the lemma you need almost certainly exists. The bad news is that it might be named something you would never guess.

**[Moogle](https://www.moogle.ai/)**: Semantic search for Mathlib. Type "triangle inequality for norms" and find `norm_add_le`. Sometimes it even understands what you meant rather than what you typed. Start here when you know what you want but not what it is called.

**[Loogle](https://loogle.lean-lang.org/)**: Type signature search. If you need a lemma involving `List.map` and `List.length`, search for `List.map, List.length` and find `List.length_map`. Precise queries get precise answers.

**In-editor tactics**: The `exact?` tactic searches for lemmas that exactly match your goal. The `apply?` tactic finds lemmas whose conclusion unifies with your goal. Slow but thorough. Use them when Moogle and Loogle fail.

**Module structure**: If you need facts about prime numbers, look in `Mathlib.Data.Nat.Prime`. If you need topology lemmas, start in `Mathlib.Topology`. The [Mathematics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html) overview provides a map of what has been formalized and where. When all else fails, grep the source code like everyone else does.

## Importing Mathlib

Most projects import Mathlib wholesale:

```lean
import Mathlib
```

This works, but your compile times will make you reconsider your life choices. For faster iteration during development, import only what you need:

```lean
{{#include ../../src/ZeroToQED/Mathlib.lean:mathlib_imports}}
```

The [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) lists all available modules. When your proof needs a specific lemma, check which module provides it and add that import. Or just import everything and go make coffee while it compiles.

## Working with Primes

Number theory in Mathlib is surprisingly pleasant. The basics are all there, and the proofs often look like what you would write on paper if paper could check your work:

```lean
{{#include ../../src/ZeroToQED/Mathlib.lean:prime_example}}
```

## Algebraic Structures

Type classes do the heavy lifting here. Declare that your type is a group, and you get inverses, identity laws, and associativity for free. Declare it is a ring, and multiplication distributes over addition without you lifting a finger:

```lean
{{#include ../../src/ZeroToQED/Mathlib.lean:algebra_example}}
```

## Real Numbers

The reals are constructed as equivalence classes of Cauchy sequences, which is mathematically clean but occasionally leaks through the abstraction when you least expect it. Most of the time you can pretend they are just numbers:

```lean
{{#include ../../src/ZeroToQED/Mathlib.lean:real_example}}
```

## Mathlib Tactics

Mathlib ships tactics that know more mathematics than most undergraduates. `ring` closes polynomial identities. `linarith` handles linear arithmetic over ordered rings. `positivity` proves things are positive. These are not magic; they are carefully engineered decision procedures. But from the outside, they look like magic:

```lean
{{#include ../../src/ZeroToQED/Mathlib.lean:tactic_example}}
```

## Using Search Tools

When stuck, let the computer do the searching. `exact?` trawls through Mathlib looking for a lemma that exactly matches your goal. `apply?` finds lemmas whose conclusion fits. These tactics are slow, but they beat staring at the screen trying to remember if the lemma is called `add_comm` or `comm_add`:

```lean
{{#include ../../src/ZeroToQED/Mathlib.lean:search_example}}
```

## The Fundamental Theorem of Calculus

The [Fundamental Theorem of Calculus](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html) in Mathlib is due to Yury Kudryashov and Benjamin Davidson. It comes in two parts, as you might remember from analysis.

The first part says that integrating then differentiating recovers the original function. If \\(f\\) is integrable and tends to \\(c\\) at \\(b\\), then the function \\(u \mapsto \int_a^u f(x)\,dx\\) has derivative \\(c\\) at \\(b\\):

```lean
theorem integral_hasStrictDerivAt_of_tendsto_ae_right
    (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (nhds b) volume)
    (hb : Tendsto f (nhds b ⊓ ae volume) (nhds c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b
```

The second part says that differentiating then integrating recovers the original function up to boundary values. If \\(f\\) is continuous on \\([a,b]\\) and differentiable on \\((a,b)\\) with integrable derivative, then:

$$\int_a^b f'(x) \, dx = f(b) - f(a)$$

```lean
theorem integral_eq_sub_of_hasDeriv_right_of_le
    (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a
```

The hypotheses handle the edge cases your calculus teacher glossed over: continuity on the closed interval, differentiability on the open interior, integrability of the derivative. Centuries of refinement, machine-checked.

## Resources

- [Moogle](https://www.moogle.ai/) - Search Mathlib using natural language queries like "triangle inequality for norms".
- [Loogle](https://loogle.lean-lang.org/) - Search by type signature when you know the shape of the lemma you need.
- [LeanSearch](https://leansearch.net/) - Semantic search over Mathlib with a focus on finding relevant theorems.
- [LeanExplore](https://leanexplore.com/) - Semantic search that also indexes metaprogramming and exposes an MCP interface for AI agents.
- [Lean Finder](https://leanfinder.github.io/) - Understands proof states and theorem statements, not just keywords.
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/) - Auto-generated API reference for every declaration in Mathlib.
- [Mathematics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html) - Map of formalized mathematics organized by mathematical area.
- [100 Theorems](https://leanprover-community.github.io/100.html) - Tracks which of 100 major theorems have been formalized in Lean.
- [Zulip Chat](https://leanprover.zulipchat.com/) - Ask questions in the "Is there code for X?" stream when search engines fail.
- [GitHub](https://github.com/leanprover-community/mathlib4) - Source code, issue tracker, and contribution guidelines.
