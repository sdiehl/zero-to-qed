# SMT Examples

Source for the `smt` tactic section of Appendix C. These examples are not part of the book's build: [lean-smt](https://github.com/ufmg-smite/lean-smt) tracks its own Lean release and downloads a cvc5 solver binary, and at the time of writing it has no revision for the Lean version this book uses.

To try them, create a Lake project on the Lean release lean-smt currently supports, add

```lean
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "main"
```

to its lakefile, and copy `SMTExamples.lean` in.
