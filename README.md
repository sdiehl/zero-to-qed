# From Zero to QED

*An informal introduction to formality.*

A best-effort knowledge transfer for learning Lean 4 the hard way.

## Read

**Online:** [sdiehl.github.io/zero-to-qed](https://sdiehl.github.io/zero-to-qed/01_introduction.html)

**PDF:** [zero-to-qed.pdf](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf) (or [print version](https://sdiehl.github.io/zero-to-qed/print.html) for browser printing)

## Table of Contents

| Chapter | Prose | Lean |
|---------|-------|------|
| Introduction | [01_introduction.md](docs/src/01_introduction.md) | |
| Why? | [02_why.md](docs/src/02_why.md) | |
| Theorem Provers | [03_theorem_provers.md](docs/src/03_theorem_provers.md) | |
| Lake Build System | [04_build_system.md](docs/src/04_build_system.md) | |
| Basics | [05_basics.md](docs/src/05_basics.md) | [Basics.lean](src/ZeroToQED/Basics.lean) |
| Control Flow | [06_control_flow.md](docs/src/06_control_flow.md) | [ControlFlow.lean](src/ZeroToQED/ControlFlow.lean) |
| Polymorphism | [07_polymorphism.md](docs/src/07_polymorphism.md) | [Polymorphism.lean](src/ZeroToQED/Polymorphism.lean) |
| Monads | [08_monads.md](docs/src/08_monads.md) | [Monads.lean](src/ZeroToQED/Monads.lean) |
| IO and Concurrency | [09_effects.md](docs/src/09_effects.md) | [Effects.lean](src/ZeroToQED/Effects.lean) |
| Proofs | [10_proving.md](docs/src/10_proving.md) | [Proving.lean](src/ZeroToQED/Proving.lean) |
| Type Theory | [11_type_theory.md](docs/src/11_type_theory.md) | [TypeTheory.lean](src/ZeroToQED/TypeTheory.lean) |
| Dependent Types | [12_dependent_types.md](docs/src/12_dependent_types.md) | |
| Proof Strategy | [13_proof_strategy.md](docs/src/13_proof_strategy.md) | |
| Tactics Reference | [14_tactics.md](docs/src/14_tactics.md) | [Tactics.lean](src/ZeroToQED/Tactics.lean) |
| Subtyping | [15_subtyping.md](docs/src/15_subtyping.md) | [Subtyping.lean](src/ZeroToQED/Subtyping.lean) |
| Classic Proofs | [16_mathematics.md](docs/src/16_mathematics.md) | [Mathematics.lean](src/ZeroToQED/Mathematics.lean) |
| Software Verification | [17_verification.md](docs/src/17_verification.md) | [Verification.lean](src/ZeroToQED/Verification.lean), [GameOfLife.lean](src/ZeroToQED/GameOfLife.lean), [StackMachine.lean](src/ZeroToQED/StackMachine.lean) |
| Artificial Intelligence | [18_artificial_intelligence.md](docs/src/18_artificial_intelligence.md) | |
| References | [19_references.md](docs/src/19_references.md) | |

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
