# Introduction

Welcome to **From Zero to QED**, an informal introduction to formality in Lean 4. This article series teaches the language from first principles. Lean is expressive but the learning resources remain scattered and incomplete. This series is a best effort to fill that gap.

> [!NOTE]
> This is the beta release. There are bound to be typos, errors, and rough edges. If you spot something, send a PR on [GitHub](https://github.com/sdiehl/zero-to-qed).

> [!TIP]
> This article is itself a giant checkable theorem. Every code sample, every proof, every definition is extracted from source files that the Lean compiler typechecks on every build. If the article compiles, the theorems are valid. The full source lives in the [GitHub repository](https://github.com/sdiehl/zero-to-qed).

## What This Series Covers

The series divides into two arcs. The first arc treats Lean as a programming language. You will learn the syntax, type system, control flow, polymorphism, monads, and IO. By the end of this arc you can write real programs in Lean.

The second arc treats Lean as a theorem prover. You will learn to write proofs, understand type theory and dependent types, master tactics, and eventually prove classic mathematical results. The series concludes with the emerging intersection of theorem proving with artificial intelligence, and why formal methods may matter more in the coming decade than they have in the previous five.

No prior experience with theorem provers is assumed. Familiarity with a typed functional language like Haskell, OCaml, or Scala helps but is not required.

## Getting Started

The full source code is available on GitHub: [github.com/sdiehl/zero-to-qed](https://github.com/sdiehl/zero-to-qed)

To run the examples locally, [install Lean 4](https://lean-lang.org/install/) and clone the repository:

```bash
git clone https://github.com/sdiehl/zero-to-qed
cd zero-to-qed
lake build
```

You can also serve the documentation locally with `just serve` if you have [mdBook](https://rust-lang.github.io/mdBook/) installed.

Additional learning resources are collected in the [References](./19_references.md) appendix. This series is an informal introduction to formality. If you want the stuffy formal introduction to formality, see [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), or university courses from [CMU](https://www.cs.cmu.edu/~mheule/15217-f21/), [Imperial](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/), and [Brown](https://browncs1951x.github.io/). They are more rigorous.
