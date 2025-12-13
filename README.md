# From Zero to QED

*An informal introduction to formality.*

A best-effort knowledge transfer for learning Lean 4 the hard way.

## Read

**Online:** [sdiehl.github.io/zero-to-qed](https://sdiehl.github.io/zero-to-qed/)

**PDF:** [zero-to-qed.pdf](https://sdiehl.github.io/zero-to-qed/zero-to-qed.pdf)

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
