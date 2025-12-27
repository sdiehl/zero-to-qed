<img src=".github/beaver.png" alt="Zero to QED" width="240">

# From Zero to QED

[![CI](https://github.com/sdiehl/zero-to-qed/actions/workflows/ci.yml/badge.svg)](https://github.com/sdiehl/zero-to-qed/actions/workflows/ci.yml)

_An informal introduction to formality in Lean 4._

## Read

- [**HTML**](https://sdiehl.github.io/zero-to-qed/01_introduction.html) - Read online
- [**PDF**](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf) - Download for offline reading

## Contents

|  # | Prose                                                             | Code                                                                                                                                                                                                       |
| -: | ----------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
|  1 | [Introduction](docs/src/01_introduction.md)                       |                                                                                                                                                                                                            |
|  2 | [Why?](docs/src/02_why.md)                                        |                                                                                                                                                                                                            |
|  3 | [Theorem Provers](docs/src/03_theorem_provers.md)                 |                                                                                                                                                                                                            |
|  4 | [Lake Build System](docs/src/04_build_system.md)                  |                                                                                                                                                                                                            |
|  5 | [Basics](docs/src/05_basics.md)                                   | [Basics.lean](src/ZeroToQED/Basics.lean)                                                                                                                                                                   |
|  6 | [Data Structures](docs/src/06_data_structures.md)                 | [DataStructures.lean](src/ZeroToQED/DataStructures.lean)                                                                                                                                                   |
|  7 | [Control Flow and Structures](docs/src/07_control_flow.md)        | [ControlFlow.lean](src/ZeroToQED/ControlFlow.lean)                                                                                                                                                         |
|  8 | [Polymorphism and Type Classes](docs/src/08_polymorphism.md)      | [Polymorphism.lean](src/ZeroToQED/Polymorphism.lean)                                                                                                                                                       |
|  9 | [Effects](docs/src/09_effects.md)                                 | [Effects.lean](src/ZeroToQED/Effects.lean)                                                                                                                                                                 |
| 10 | [IO and Concurrency](docs/src/10_io.md)                           | [IO.lean](src/ZeroToQED/IO.lean)                                                                                                                                                                           |
| 11 | [Proofs](docs/src/11_proving.md)                                  | [Proving.lean](src/ZeroToQED/Proving.lean)                                                                                                                                                                 |
| 12 | [Type Theory](docs/src/12_type_theory.md)                         | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean)                                                                                                                                                           |
| 13 | [Dependent Types](docs/src/13_dependent_types.md)                 | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean), [DependentTypes.lean](src/ZeroToQED/DependentTypes.lean)                                                                                                 |
| 14 | [Proof Strategy](docs/src/14_proof_strategy.md)                   | [ProofStrategy.lean](src/ZeroToQED/ProofStrategy.lean)                                                                                                                                                     |
| 15 | [Tactics Reference](docs/src/15_tactics.md)                       | [Tactics.lean](src/ZeroToQED/Tactics.lean)                                                                                                                                                                 |
| 16 | [Congruence and Subtyping](docs/src/16_subtyping.md)              | [Subtyping.lean](src/ZeroToQED/Subtyping.lean)                                                                                                                                                             |
| 17 | [Classic Proofs](docs/src/17_mathematics.md)                      | [Proofs/](src/ZeroToQED/Proofs/)                                                                                                                                                                           |
| 18 | [Algebraic Structures](docs/src/18_algebraic_structures.md)       | [AlgebraicStructures.lean](src/ZeroToQED/AlgebraicStructures.lean)                                                                                                                                         |
| 19 | [Mathlib](docs/src/19_mathlib.md)                                 | [Mathlib.lean](src/ZeroToQED/Mathlib.lean)                                                                                                                                                                 |
| 20 | [Software Verification](docs/src/20_verification.md)              | [Verification.lean](src/ZeroToQED/Verification.lean), [Compiler.lean](src/ZeroToQED/Compiler.lean), [GameOfLife.lean](src/ZeroToQED/GameOfLife.lean), [StackMachine.lean](src/ZeroToQED/StackMachine.lean) |
| 21 | [Artificial Intelligence](docs/src/21_artificial_intelligence.md) | [Auction.lean](src/ZeroToQED/Auction.lean), [Vickrey.lean](src/ZeroToQED/Vickrey.lean), [CombinatorialAuction.lean](src/ZeroToQED/CombinatorialAuction.lean)                                               |
| 22 | [References](docs/src/22_references.md)                           |                                                                                                                                                                                                            |

## Build

```bash
git clone https://github.com/sdiehl/zero-to-qed
cd zero-to-qed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cargo install mdbook
```

## And then...

```bash
just build          # Build Lean project
just test           # Run tests
just run            # Run executable
just format         # Format code (cargo fmt + dprint)
just serve          # Serve docs locally
just gen-svg        # Generate procedural SVG illustrations
just build-docs     # Build HTML documentation (runs gen-svg first)
just pdf            # Build PDF via typst
just open-pdf       # Open the generated PDF
just clean          # Clean build artifacts
just update         # Update dependencies
just stats          # Project statistics
```

## Contributing

See [BUILD.md](BUILD.md) for details on the HTML and PDF build pipeline. Add yourself to [CONTRIBUTORS.md](CONTRIBUTORS.md) and submit a PR.

## License

**Software** (Lean code in `src/`): MIT License. See [LICENSE](LICENSE).

**Prose** (text in `docs/`): Public domain. Share it, adapt it, translate it. I just ask that you not sell it. It is meant to be free.
