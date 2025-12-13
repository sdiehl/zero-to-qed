# From Zero to QED

From Zero to QED: A quirky introduction to theorem proving and dependent types
from first principles.

## Install

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cargo install mdbook mdbook-katex
```

## Commands

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

**Software** (Lean source code in `src/`): MIT License. See [LICENSE](LICENSE).

**Prose** (documentation in `docs/`): Public domain. Share it, adapt it, translate it. I just ask that you not sell it. It is meant to be free.
