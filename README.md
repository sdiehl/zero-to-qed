# From Zero to QED

*An informal introduction to formality.*

A best-effort knowledge transfer for learning Lean 4 the hard way.

## Read

**Online:** [sdiehl.github.io/zero-to-qed](https://sdiehl.github.io/zero-to-qed/01_introduction.html)

**PDF:** [zero-to-qed.pdf](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf) (or [print version](https://sdiehl.github.io/zero-to-qed/print.html) for browser printing)

## Contents

| Prose | Code |
|---|---|
| [Introduction](docs/src/01_introduction.md) | |
| [Why?](docs/src/02_why.md) | |
| [Theorem Provers](docs/src/03_theorem_provers.md) | |
| [Build System](docs/src/04_build_system.md) | |
| [Basics](docs/src/05_basics.md) | [Basics.lean](src/ZeroToQED/Basics.lean) |
| [Control Flow](docs/src/06_control_flow.md) | [ControlFlow.lean](src/ZeroToQED/ControlFlow.lean) |
| [Polymorphism](docs/src/07_polymorphism.md) | [Polymorphism.lean](src/ZeroToQED/Polymorphism.lean) |
| [Monads](docs/src/08_monads.md) | [Monads.lean](src/ZeroToQED/Monads.lean) |
| [Effects](docs/src/09_effects.md) | [Effects.lean](src/ZeroToQED/Effects.lean) |
| [Proofs](docs/src/10_proving.md) | [Proving.lean](src/ZeroToQED/Proving.lean) |
| [Type Theory](docs/src/11_type_theory.md) | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean) |
| [Dependent Types](docs/src/12_dependent_types.md) | |
| [Proof Strategy](docs/src/13_proof_strategy.md) | |
| [Tactics](docs/src/14_tactics.md) | [Tactics.lean](src/ZeroToQED/Tactics.lean) |
| [Subtyping](docs/src/15_subtyping.md) | [Subtyping.lean](src/ZeroToQED/Subtyping.lean) |
| [Mathematics](docs/src/16_mathematics.md) | [Mathematics.lean](src/ZeroToQED/Mathematics.lean) |
| [Verification](docs/src/17_verification.md) | [Verification.lean](src/ZeroToQED/Verification.lean), [GameOfLife.lean](src/ZeroToQED/GameOfLife.lean), [StackMachine.lean](src/ZeroToQED/StackMachine.lean) |
| [AI](docs/src/18_artificial_intelligence.md) | |
| [References](docs/src/19_references.md) | |

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
