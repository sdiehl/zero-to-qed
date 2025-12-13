# Introduction

Welcome to From Zero to QED, an article series that teaches Lean 4 from first principles. This is the tutorial I wish I had when I started learning Lean. The language is powerful but the learning resources remain scattered and incomplete. This series aims to fill that gap.

> [!TIP]
> This article series is itself a Lean project. Every code sample, every proof, every theorem is extracted from source files that the Lean compiler typechecks on every build. The text you are reading is backed by machine-verified code in the [GitHub repository](https://github.com/sdiehl/zero-to-qed). Call it a literate proof.

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

Additional learning resources are collected in the [References](./19_references.md) appendix.
