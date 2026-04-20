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

There are several ways to follow along with the examples, from zero-install browser options to full local setup.

### Option 1: Browser

[Lean Live](https://live.lean-lang.org/) runs Lean 4 in your browser with no installation. Copy code snippets from the text and paste them into the editor. For compatibility with examples in this series, set the toolchain to `leanprover/lean4:v4.28.0` and Mathlib to `v4.28.0` in the settings. Some later articles require Mathlib, which Lean Live supports but loads slowly on first use.

### Option 2: One-Click Cloud Environment

Launch a complete Lean 4 environment in your browser with no local setup:

- [**Open in GitHub Codespaces**](https://codespaces.new/sdiehl/zero-to-qed) - Free for 120 core-hours/month
- [**Open in Gitpod**](https://gitpod.io/#https://github.com/sdiehl/zero-to-qed) - Free tier available

Both options provide VS Code in the browser with Lean 4, the language extension, and all dependencies pre-installed. The environment runs `lake exe cache get` automatically on startup to download prebuilt Mathlib artifacts.

### Option 3: Dev Container (Docker + VS Code)

If you have Docker and VS Code installed locally, clone the repo and open it in VS Code:

```bash
git clone https://github.com/sdiehl/zero-to-qed
code zero-to-qed
```

VS Code will detect the `.devcontainer` configuration and prompt you to "Reopen in Container". This builds the same environment locally, giving you cloud-like convenience with local performance.

### Option 4: Local Installation

For the full experience, [install Lean 4](https://lean-lang.org/install/) with VS Code and the Lean 4 extension. Other editors work too (Zed, Emacs, Neovim all have Lean support) but VS Code is the best documented and most widely used. Clone the repository:

```bash
git clone https://github.com/sdiehl/zero-to-qed
cd zero-to-qed
lake exe cache get   # Download prebuilt Mathlib (saves hours)
lake build
```

The `lake exe cache get` command downloads prebuilt artifacts for Mathlib, reducing the initial build from hours to minutes. Without it, Lake compiles Mathlib from source, which tests your patience more than your code.

You can also serve the documentation locally with `just serve` if you have [mdBook](https://rust-lang.github.io/mdBook/) installed.

## Reading Paths

Different readers come to this material with different goals. Here are suggested paths through the series:

**Complete beginners to typed functional programming**: Read linearly. Arc I builds the programming foundation you need. Do not skip ahead to proofs until you are comfortable with pattern matching, recursion, and type classes. The concepts in [Polymorphism](./09_polymorphism.md) are essential for understanding how Lean's type system works.

**Systems programmers wanting verification**: Read Arc I thoroughly since you will use these features in production code. In Arc II, focus on [Proofs](./12_proving.md), [Proof Strategy](./15_proof_strategy.md), [Verified Programs](./20_verified_programs.md), and [Model Checking](./21_model_checking.md). The [Type Theory](./13_type_theory.md) article provides the foundation but can be revisited as needed.

**AI researchers interested in theorem proving**: After covering the basics, jump to [Proofs](./12_proving.md), then [Tactics Reference](./appendix_c_tactics.md), and finally [Artificial Intelligence](./22_artificial_intelligence.md). The intermediate articles on type theory and algebraic structures can wait until you need them for specific formalization tasks.

**Mathematicians new to programming**: Start with [Basics](./04_basics.md) and [Control Flow](./07_control_flow.md) to learn Lean as a language, then proceed linearly through Arc II. You may skim [Effects](./10_effects.md) and [IO](./11_io.md) on first reading since they focus on computational side effects rather than proof.

**Article dependencies**: Most articles build on previous ones, but some can be read independently. [Classic Proofs](./17_mathematics.md) requires only [Proofs](./12_proving.md) and [Proof Strategy](./15_proof_strategy.md). [Algebraic Structures](./18_algebraic_structures.md) requires [Type Classes](./09_polymorphism.md). [Mathlib](./19_mathlib.md) requires familiarity with tactics from earlier articles but not deep type theory.

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

Additional learning resources are collected in the [References](./23_references.md) appendix. This series is an informal introduction to formality. If you want the stuffy formal introduction to formality, see [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), or university courses from [CMU](https://www.cs.cmu.edu/~mheule/15217-f21/), [Imperial](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/), and [Brown](https://browncs1951x.github.io/). They are more rigorous.
