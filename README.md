<img src=".github/beaver.png" alt="Zero to QED" width="240">

# From Zero to QED

[![CI](https://github.com/sdiehl/zero-to-qed/actions/workflows/ci.yml/badge.svg)](https://github.com/sdiehl/zero-to-qed/actions/workflows/ci.yml)

_An informal introduction to formality in Lean 4._

## Read

- [**HTML**](https://sdiehl.github.io/zero-to-qed/01_introduction.html) - Read online
- [**PDF**](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf) - Download for offline reading

## Try Online

No local setup required. Launch a complete Lean 4 environment in your browser:

- [**Open in GitHub Codespaces**](https://codespaces.new/sdiehl/zero-to-qed) - Free for 120 core-hours/month
- [**Open in Gitpod**](https://gitpod.io/#https://github.com/sdiehl/zero-to-qed) - Free tier available

The environment comes pre-configured with Lean 4, the VS Code extension, and all dependencies.

## Try Locally

[Install Lean 4](https://lean-lang.org/install/) with VS Code and the Lean 4 extension, then:

```bash
git clone https://github.com/sdiehl/zero-to-qed
cd zero-to-qed
lake exe cache get   # Download prebuilt Mathlib
lake build
```

Alternatively, if you have Docker and VS Code installed, clone the repo and open it in VS Code. You'll be prompted to "Reopen in Container" which builds the same environment on your machine.

## Contents

|  # | Prose                                                             | Code                                                                                                                                                                                                                                                                                                                                |
| -: | ----------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
|  1 | [Introduction](docs/src/01_introduction.md)                       |                                                                                                                                                                                                                                                                                                                                     |
|  2 | [Why?](docs/src/02_why.md)                                        |                                                                                                                                                                                                                                                                                                                                     |
|  3 | [Theorem Provers](docs/src/03_theorem_provers.md)                 |                                                                                                                                                                                                                                                                                                                                     |
|  4 | [Basics](docs/src/04_basics.md)                                   | [Basics.lean](src/ZeroToQED/Basics.lean)                                                                                                                                                                                                                                                                                            |
|  5 | [Lake Build System](docs/src/05_build_system.md)                  |                                                                                                                                                                                                                                                                                                                                     |
|  6 | [Data Structures](docs/src/06_data_structures.md)                 | [DataStructures.lean](src/ZeroToQED/DataStructures.lean), [MagicTheGathering.lean](src/Examples/MagicTheGathering.lean)                                                                                                                                                                                                             |
|  7 | [Control Flow and Structures](docs/src/07_control_flow.md)        | [ControlFlow.lean](src/ZeroToQED/ControlFlow.lean), [FizzBuzz.lean](src/Examples/FizzBuzz.lean), [Collatz.lean](src/Examples/Collatz.lean), [DndCharacter.lean](src/Examples/DndCharacter.lean)                                                                                                                                     |
|  8 | [Standard Library and Batteries](docs/src/08_stdlib.md)           | [StdLibrary.lean](src/ZeroToQED/StdLibrary.lean)                                                                                                                                                                                                                                                                                    |
|  9 | [Polymorphism and Type Classes](docs/src/09_polymorphism.md)      | [Polymorphism.lean](src/ZeroToQED/Polymorphism.lean), [SpellEffects.lean](src/Examples/SpellEffects.lean), [Units.lean](src/Examples/Units.lean)                                                                                                                                                                                    |
| 10 | [Effects](docs/src/10_effects.md)                                 | [Effects.lean](src/ZeroToQED/Effects.lean), [ATM.lean](src/Examples/ATM.lean)                                                                                                                                                                                                                                                       |
| 11 | [IO and Concurrency](docs/src/11_io.md)                           | [IO.lean](src/ZeroToQED/IO.lean), [WordFreq.lean](src/Examples/WordFreq.lean)                                                                                                                                                                                                                                                       |
| 12 | [Proofs](docs/src/12_proving.md)                                  | [Proving.lean](src/ZeroToQED/Proving.lean)                                                                                                                                                                                                                                                                                          |
| 13 | [Type Theory](docs/src/13_type_theory.md)                         | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean)                                                                                                                                                                                                                                                                                    |
| 14 | [Dependent Types](docs/src/14_dependent_types.md)                 | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean), [DependentTypes.lean](src/ZeroToQED/DependentTypes.lean), [VendingMachine.lean](src/Examples/VendingMachine.lean), [NQueens.lean](src/Examples/NQueens.lean)                                                                                                                      |
| 15 | [Proof Strategy](docs/src/15_proof_strategy.md)                   | [ProofStrategy.lean](src/ZeroToQED/ProofStrategy.lean)                                                                                                                                                                                                                                                                              |
| 16 | [Congruence and Subtyping](docs/src/16_subtyping.md)              | [Subtyping.lean](src/ZeroToQED/Subtyping.lean)                                                                                                                                                                                                                                                                                      |
| 17 | [Classic Proofs](docs/src/17_mathematics.md)                      | [Proofs/](src/ZeroToQED/Proofs/)                                                                                                                                                                                                                                                                                                    |
| 18 | [Algebraic Structures](docs/src/18_algebraic_structures.md)       | [AlgebraicStructures.lean](src/ZeroToQED/AlgebraicStructures.lean)                                                                                                                                                                                                                                                                  |
| 19 | [Mathlib](docs/src/19_mathlib.md)                                 | [Mathlib.lean](src/ZeroToQED/Mathlib.lean)                                                                                                                                                                                                                                                                                          |
| 20 | [Verified Programs](docs/src/20_verified_programs.md)             | [Verification.lean](src/ZeroToQED/Verification.lean), [Compiler.lean](src/ZeroToQED/Compiler.lean), [GameOfLife.lean](src/ZeroToQED/GameOfLife.lean), [StackMachine.lean](src/ZeroToQED/StackMachine.lean), [CircuitBreaker.lean](src/ZeroToQED/CircuitBreaker.lean), [ParserCombinators.lean](src/Examples/ParserCombinators.lean) |
| 21 | [Model Checking](docs/src/21_model_checking.md)                   | [ModelChecking.lean](src/ZeroToQED/ModelChecking.lean)                                                                                                                                                                                                                                                                              |
| 22 | [Artificial Intelligence](docs/src/22_artificial_intelligence.md) | [Auction.lean](src/ZeroToQED/Auction.lean), [Vickrey.lean](src/ZeroToQED/Vickrey.lean), [CombinatorialAuction.lean](src/ZeroToQED/CombinatorialAuction.lean)                                                                                                                                                                        |
| 23 | [References](docs/src/23_references.md)                           |                                                                                                                                                                                                                                                                                                                                     |

## Contributing

See [BUILD.md](BUILD.md) for details on the HTML and PDF build pipeline. Add yourself to [CONTRIBUTORS.md](CONTRIBUTORS.md) and submit a PR.

## License

**Software** (Lean code in `src/`): MIT License. See [LICENSE](LICENSE).

**Prose** (text in `docs/`): Public domain. Share it, adapt it, translate it. I just ask that you not sell it. It is meant to be free.
