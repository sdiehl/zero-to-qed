# Appendix D: Writing Durable Lean

A proof that compiles today is not the same as a proof that will compile after the next toolchain bump, or that a colleague can read in six months. Automation makes this worse, not better: an opaque call that happens to work carries no record of why. The following conventions come from maintaining large Lean codebases in production, and most of them can be enforced mechanically by a linter or by project settings.

**Turn off auto-bound implicits.** By default Lean treats an unknown single-letter identifier in a signature as an implicit argument, and with `relaxedAutoImplicit` any unknown identifier at all. A typo in a theorem statement then becomes a fresh universally quantified variable instead of an error, and the theorem compiles while proving something other than what it says. Disable both in the package, as this book's own `lakefile.lean` does:

```lean
package MyProject where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]
```

In a `lakefile.toml` the same settings are `leanOptions = { autoImplicit = false, relaxedAutoImplicit = false, warningAsError = true }`. Every variable then has to be bound explicitly, with a `variable` declaration or in the signature.

**Treat warnings as errors.** Lean's own linters report through warnings: unused hypotheses, unused `simp` arguments, deprecated lemmas, unreachable branches. A build that tolerates warnings tolerates all of these equally. Set `warningAsError` and silence the specific ones worth keeping at the declaration that needs them.

**Pin your automation.** A bare `simp` closes its goal against whatever the default simp set holds, and a toolchain bump can change that set. Worse is a rewrite or `apply` that runs against the goal an unpinned `simp` left behind, since then the following step depends on the exact normal form. Use `simp?` to find the lemmas and commit the resulting `simp only [...]`. The same applies to `grind?` and `grind only`, and to the search tactics: `exact?`, `apply?`, `hint`, and `try?` are how a proof is _found_, not how it should be _written_. They rerun the search on every build. Paste what they suggest and delete the question mark.

**Keep proofs small and named.** A long proof with deeply nested blocks forces the reader to hold a large goal state in their head. When a `have` spans many tactics, lift it into its own lemma. When the same proof script appears twice, name it once and apply it in both places. When a goal split produces several cases, use `case` tags rather than anonymous `·` bullets beneath another split, so that each block says which goal it closes and survives a reordering of the constructors.

**Mark your trust boundaries.** `sorry` introduces `sorryAx`; an `axiom` adds an assumption; `native_decide` relies on compiled evaluation and generated axioms. Use `#print axioms` on top-level theorems and check the result against your project’s allowed assumptions. An `opaque` declaration with a body is still checked and introduces no axiom merely by hiding reduction. An `unsafe` implementation cannot be used directly in a safe proof; relying on compiled execution can nevertheless enlarge the trusted base. Classical reasoning inside a proof is erased, while a definition that uses `Classical.choice` to produce data is noncomputable.

**Leave no scratch commands behind.** `#eval`, `#check`, and `#reduce` run on every build and report to nobody. A fact worth keeping should be a theorem, a `#guard`, or a `#guard_msgs` test that fails when the output changes. `#print axioms` is the exception worth leaving in.

**Name things by kind.** Lean's conventions encode what a declaration is: theorems and lemmas in `snake_case` (`add_comm`, `size_pos`), types and structures in `UpperCamelCase` (`HashMap`), and definitions and functions in `lowerCamelCase`. The name should say what the declaration is about, not restate the whole statement; the statement belongs in a docstring above it.

**Keep modules narrow.** Mark helper lemmas `private` so that other modules cannot come to depend on your working steps. Give every public declaration a docstring. Split a file when it grows past one sitting of reading or when its declarations stop sharing imports. Avoid deep `extends` chains in structures, since every field of a parent becomes a field of the child and the value's shape can no longer be read from one declaration. Prefer writing tactics out, or naming a lemma, over defining custom tactic macros; a macro is a new language the reader has to learn before they can read the proof.

None of this is specific to one tactic, but it is the discipline that makes heavy automation safe. Pinned calls, explicit variables, and small named lemmas are what let you bump the toolchain, rerun the build, and trust that a green build still means what it meant yesterday.
