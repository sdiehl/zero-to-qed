# Introduction

Welcome to **From Zero to QED**, an informal introduction to formality in Lean 4. This article series teaches the language from first principles. Lean is expressive but the learning resources remain scattered and incomplete. This series is a best effort to fill that gap.

**[Read Online](https://sdiehl.github.io/zero-to-qed/)** | **[Download PDF](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf)**

> [!NOTE]
> This is the beta release. There are bound to be typos, errors, and rough edges. If you spot something, send a PR on [GitHub](https://github.com/sdiehl/zero-to-qed).

> [!TIP]
> This article is itself a giant checkable theorem. Every code sample, every proof, every definition is extracted from source files that the Lean compiler typechecks on every build. If the article compiles, the theorems are valid. The full source lives in the [GitHub repository](https://github.com/sdiehl/zero-to-qed).

## What This Series Covers

The series divides into two arcs. The first arc treats Lean as a programming language. You will learn the syntax, type system, control flow, polymorphism, monads, and IO. By the end of this arc you can write real programs in Lean.

The second arc treats Lean as a **theorem prover**. You will learn to write proofs, understand **type theory** and **dependent types**, master **tactics**, and eventually prove classic mathematical results. The series concludes with the emerging intersection of theorem proving with artificial intelligence, and why formal methods may matter more in the coming decade than they have in the previous five.

No prior experience with theorem provers is assumed. Familiarity with a typed functional language like Haskell, OCaml, or Scala helps but is not strictly required.

## Getting Started

Follow the [official Lean installation instructions](https://lean-lang.org/install/).

## Reading Paths

Different readers come to this material with different goals. Here are suggested paths through the series:

**Complete beginners to typed functional programming**: Read linearly. Arc I builds the programming foundation you need. Do not skip ahead to proofs until you are comfortable with pattern matching, recursion, and type classes. The concepts in [Polymorphism](./10_polymorphism.md) are essential for understanding how Lean's type system works.

**Systems programmers wanting verification**: Read Arc I thoroughly since you will use these features in production code. In Arc II, focus on [Proofs](./13_proving.md), [Proof Strategy](./16_proof_strategy.md), [Verified Programs](./21_verified_programs.md), and [Model Checking](./22_model_checking.md). The [Type Theory](./14_type_theory.md) article provides the foundation but can be revisited as needed.

**AI researchers interested in theorem proving**: After covering the basics, jump to [Proofs](./13_proving.md), then [Tactics Reference](./appendix_c_tactics.md), and finally [Artificial Intelligence](./23_artificial_intelligence.md). The intermediate articles on type theory and algebraic structures can wait until you need them for specific formalization tasks.

**Mathematicians new to programming**: Start with [Basics](./04_basics.md) and [Control Flow](./07_control_flow.md) to learn Lean as a language, then proceed linearly through Arc II. You may skim [Effects](./11_effects.md) and [IO](./12_io.md) on first reading since they focus on computational side effects rather than proof.

**Article dependencies**: Most articles build on previous ones, but some can be read independently. [Classic Proofs](./18_mathematics.md) requires only [Proofs](./13_proving.md) and [Proof Strategy](./16_proof_strategy.md). [Algebraic Structures](./19_algebraic_structures.md) requires [Type Classes](./10_polymorphism.md). [Mathlib](./20_mathlib.md) requires familiarity with tactics from earlier articles but not deep type theory.

## Repository Structure

Code samples are extracted from Lean source files. Each article corresponds to modules in the `src/` directory:

| Article         | Source File                                                                                                            |
| --------------- | ---------------------------------------------------------------------------------------------------------------------- |
| Basics          | [src/ZeroToQED/Basics.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Basics.lean)                 |
| Data Structures | [src/ZeroToQED/DataStructures.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/DataStructures.lean) |
| Control Flow    | [src/ZeroToQED/ControlFlow.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/ControlFlow.lean)       |
| Polymorphism    | [src/ZeroToQED/Polymorphism.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Polymorphism.lean)     |
| Effects         | [src/ZeroToQED/Effects.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Effects.lean)               |
| IO              | [src/ZeroToQED/IO.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/IO.lean)                         |
| Proofs          | [src/ZeroToQED/Proving.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Proving.lean)               |
| Type Theory     | [src/ZeroToQED/TypeTheory.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/TypeTheory.lean)         |
| Tactics         | [src/ZeroToQED/Tactics.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Tactics.lean)               |

Larger examples live in `src/Examples/`:

| Example                 | Source File                                                                                                   | Run Command                     |
| ----------------------- | ------------------------------------------------------------------------------------------------------------- | ------------------------------- |
| Magic: The Gathering    | [MagicTheGathering.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/MagicTheGathering.lean) | `lake exe mtg`                  |
| D&D Character Generator | [DndCharacter.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/DndCharacter.lean)           | `lake exe dnd 42`               |
| ATM Withdrawal          | [ATM.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/ATM.lean)                             | `lake exe atm`                  |
| Parser Combinators      | [ParserCombinators.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/ParserCombinators.lean) | `lake exe parsers`              |
| Game of Life            | [GameOfLife.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/GameOfLife.lean)              | `lake exe life`                 |
| Stack Machine           | [StackMachine.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/StackMachine.lean)          | `lake exe stack`                |
| Circuit Breaker         | [CircuitBreaker.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/CircuitBreaker.lean)      | `cargo test -p circuit-breaker` |

Open these files in VS Code to explore with full IDE support. The Infoview panel shows types and proof states as you navigate.

Additional learning resources are collected in the [References](./24_references.md) appendix. This series is an informal introduction to formality. If you want the stuffy formal introduction to formality, see [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), or university courses from [CMU](https://www.cs.cmu.edu/~mheule/15217-f21/), [Imperial](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/), and [Brown](https://browncs1951x.github.io/). They are more rigorous.
