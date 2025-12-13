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
just build        # Build Lean project
just serve        # Serve docs locally
```

## License

**Software** (Lean code in `src/`): MIT License. See [LICENSE](LICENSE).

**Prose** (text in `docs/`): Public domain. Share it, adapt it, translate it. I just ask that you not sell it. It is meant to be free.
