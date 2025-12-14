# From Zero to QED

*An informal introduction to formality in Lean 4.*

## Read

**Read Online:** [sdiehl.github.io/zero-to-qed](https://sdiehl.github.io/zero-to-qed/01_introduction.html)

**PDF:** [zero-to-qed.pdf](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf) (or [print version](https://sdiehl.github.io/zero-to-qed/print.html) for browser printing)

## Contents

| # | Prose | Code |
|--:|-------|------|
| 1 | [Introduction](docs/src/01_introduction.md) | |
| 2 | [Why?](docs/src/02_why.md) | |
| 3 | [Theorem Provers](docs/src/03_theorem_provers.md) | |
| 4 | [Build System](docs/src/04_build_system.md) | |
| 5 | [Basics](docs/src/05_basics.md) | [Basics.lean](src/ZeroToQED/Basics.lean) |
| 6 | [Control Flow](docs/src/06_control_flow.md) | [ControlFlow.lean](src/ZeroToQED/ControlFlow.lean) |
| 7 | [Polymorphism](docs/src/07_polymorphism.md) | [Polymorphism.lean](src/ZeroToQED/Polymorphism.lean) |
| 8 | [Effects](docs/src/08_effects.md) | [Monads.lean](src/ZeroToQED/Monads.lean) |
| 9 | [IO and Concurrency](docs/src/09_effects.md) | [Effects.lean](src/ZeroToQED/Effects.lean) |
| 10 | [Proofs](docs/src/10_proving.md) | [Proving.lean](src/ZeroToQED/Proving.lean) |
| 11 | [Type Theory](docs/src/11_type_theory.md) | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean) |
| 12 | [Dependent Types](docs/src/12_dependent_types.md) | [DependentTypes.lean](src/ZeroToQED/DependentTypes.lean) |
| 13 | [Proof Strategy](docs/src/13_proof_strategy.md) | [ProofStrategy.lean](src/ZeroToQED/ProofStrategy.lean) |
| 14 | [Tactics](docs/src/14_tactics.md) | [Tactics.lean](src/ZeroToQED/Tactics.lean) |
| 15 | [Subtyping](docs/src/15_subtyping.md) | [Subtyping.lean](src/ZeroToQED/Subtyping.lean) |
| 16 | [Mathematics](docs/src/16_mathematics.md) | [Mathematics.lean](src/ZeroToQED/Mathematics.lean) |
| 17 | [Mathlib](docs/src/17_mathlib.md) | [Mathlib.lean](src/ZeroToQED/Mathlib.lean) |
| 18 | [Verification](docs/src/18_verification.md) | [Verification.lean](src/ZeroToQED/Verification.lean), [GameOfLife.lean](src/ZeroToQED/GameOfLife.lean), [StackMachine.lean](src/ZeroToQED/StackMachine.lean) |
| 19 | [AI](docs/src/19_artificial_intelligence.md) | |
| 20 | [References](docs/src/20_references.md) | |

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
just serve          # Serve docs locally
just build-docs     # Build documentation
just dev            # Lint, build, test
just ci             # Full CI checks
just clean          # Clean build artifacts
just update         # Update dependencies
just stats          # Project statistics
```

## License

**Software** (Lean code in `src/`): MIT License. See [LICENSE](LICENSE).

**Prose** (text in `docs/`): Public domain. Share it, adapt it, translate it. I just ask that you not sell it. It is meant to be free.
