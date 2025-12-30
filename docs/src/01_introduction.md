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

> [!TIP]
> No installation required to get started: [Lean Live](https://live.lean-lang.org/) runs Lean 4 in your browser.

The full source code is available on GitHub: [github.com/sdiehl/zero-to-qed](https://github.com/sdiehl/zero-to-qed)

To run the examples locally, [install Lean 4](https://lean-lang.org/install/) and clone the repository:

```bash
git clone https://github.com/sdiehl/zero-to-qed
cd zero-to-qed
lake exe cache get   # Download prebuilt Mathlib (saves hours)
lake build
```

The `lake exe cache get` command downloads prebuilt artifacts for Mathlib, reducing the initial build from hours to minutes. Without it, Lake compiles Mathlib from source, which tests your patience more than your code.

You can also serve the documentation locally with `just serve` if you have [mdBook](https://rust-lang.github.io/mdBook/) installed.

## Repository Structure

Code samples are extracted from Lean source files. Each chapter corresponds to modules in the `src/` directory:

| Chapter         | Source File                                                                                                            |
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

| Example                 | Source File                                                                                                   | Run Command       |
| ----------------------- | ------------------------------------------------------------------------------------------------------------- | ----------------- |
| Magic: The Gathering    | [MagicTheGathering.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/MagicTheGathering.lean) | `lake exe mtg`    |
| D&D Character Generator | [DndCharacter.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/Examples/DndCharacter.lean)           | `lake exe dnd 42` |
| Game of Life            | [GameOfLife.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/GameOfLife.lean)              | `lake exe life`   |
| Stack Machine           | [StackMachine.lean](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/StackMachine.lean)          | -                 |

Open these files in VS Code to explore with full IDE support. The Infoview panel shows types and proof states as you navigate.

Additional learning resources are collected in the [References](./22_references.md) appendix. This series is an informal introduction to formality. If you want the stuffy formal introduction to formality, see [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), or university courses from [CMU](https://www.cs.cmu.edu/~mheule/15217-f21/), [Imperial](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/), and [Brown](https://browncs1951x.github.io/). They are more rigorous.
