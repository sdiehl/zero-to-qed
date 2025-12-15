# Theorem Provers

*This article covers the landscape of theorem provers and why Lean won. If you do not care about context, skip to [Basics](./05_basics.md).*

Theorem provers have existed since the 1960s. Most of them failed to escape academia. A few succeeded spectacularly. Understanding why some won and others lost clarifies what makes Lean different.

## The Graveyard

Most theorem provers die the same death: they work, but nobody uses them. The software is correct, the theory is sound, the papers get cited, and then the maintainer graduates or retires and the codebase rots. This is not a failure of engineering. It is a failure of ecosystem.

A theorem prover without a library is a programming language without packages. You can write everything from scratch, but you will not. The activation energy is too high. [Automath](https://en.wikipedia.org/wiki/Automath) proved you could encode mathematics in the 1960s. [Mizar](https://en.wikipedia.org/wiki/Mizar_system) built a large library but with a syntax that looks like it was designed to repel newcomers. The [Boyer-Moore](https://en.wikipedia.org/wiki/Nqthm) provers achieved industrial success at AMD but never grew a community. Each system had technical merit. None achieved escape velocity.

## The Survivors

Three theorem provers dominate today: [Coq](https://en.wikipedia.org/wiki/Coq_(software)), [Isabelle](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant)), and Lean. Each survived because of a killer app.

**Coq** (1984) survived because of [CompCert](https://en.wikipedia.org/wiki/CompCert), a verified C compiler that proved you could extract real software from proofs. When people asked "but can you build anything real?" the answer was a production compiler. Coq also proved the [four color theorem](https://en.wikipedia.org/wiki/Four_color_theorem), giving mathematicians a reason to care.

**Isabelle** (1986) survived because of [seL4](https://en.wikipedia.org/wiki/SeL4), a verified operating system kernel that proved formal methods could handle systems software. When people asked "but does it scale?" the answer was 10,000 lines of verified C.

**Lean** (2013) is surviving because of [Mathlib](https://en.wikipedia.org/wiki/Mathlib). At 1.9 million lines, it is the largest coherent mathematical library ever created. When people ask "but can I formalize real mathematics?" the answer is: probably someone already did, go look it up. Mathlib is Lean's moat.

## Why Lean Is Winning Now

Lean 4 shipped in 2021 as a ground-up rewrite. Several things went right:

**Speed.** Lean 4 compiles to C and runs fast. Not "fast for a theorem prover" but actually fast. You can write command-line tools, build systems, even games. Coq and Isabelle are sluggish by comparison. This matters because proof assistants are IDEs, and IDE responsiveness determines whether people finish their proofs or give up.

**Metaprogramming.** Lean 4's tactic framework is written in Lean itself. You can inspect it, modify it, and write your own tactics without learning a separate metalanguage. In Coq, the tactic language (Ltac) is a different beast from the term language. In Lean, tactics are just programs.

**Syntax.** Lean looks like a normal programming language. Functions are functions. Pattern matching works how you expect. Unicode is optional. Compare this to Coq's baroque notation system or Isabelle's ASCII-art syntax. Lower friction means more users.

**Community momentum.** Mathlib grows by thousands of theorems monthly. The [Lean Zulip](https://leanprover.zulipchat.com/) is active and welcoming. [Kevin Buzzard](https://www.imperial.ac.uk/people/k.buzzard) teaches undergraduates at Imperial. [Terence Tao](https://terrytao.wordpress.com/) formalizes his papers. When Fields medalists use your tool, others follow.

**AI integration.** Lean is the default target for neural theorem proving research. [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover), [LeanDojo](https://leandojo.org/), and others chose Lean because the metaprogramming API makes tool integration tractable. This creates a flywheel: more AI tooling attracts more users attracts more AI tooling.

## The Also-Rans

**[Agda](https://en.wikipedia.org/wiki/Agda_(programming_language))** is beautiful. Its dependent pattern matching influenced Lean's design. It supports cubical type theory for people who care about homotopy. But Agda has no substantial mathematical library, which means every project starts from scratch. It remains a research vehicle.

**[Idris](https://en.wikipedia.org/wiki/Idris_(programming_language))** pioneered practical dependent types for programming. Many of its ergonomic ideas appear in Lean 4. But Idris 2 is maintained by essentially one person, and there is no community building a shared library. It is a glimpse of a future that Lean is actually building.

**[HOL family](https://en.wikipedia.org/wiki/HOL_(proof_assistant))** (HOL4, HOL Light, Isabelle/HOL) use simpler type theories without full dependent types. This makes automation easier but specifications harder. You cannot express "a list of length n" directly in HOL. These systems thrive in hardware verification niches but struggle with mathematics.

## The Bottom Line

Lean won for the same reason Python won: it was good enough technically and better socially. The syntax is approachable. The tooling is modern. The library is massive. The community is active. When a Fields medalist and a trading firm and an AI lab all independently choose the same tool, something real is happening.

If you are starting today, start with Lean. The alternatives are not wrong, but they are lonelier.

If you want the theoretical foundations: [Type Theory](./11_type_theory.md) covers the core calculus. [Dependent Types](./12_dependent_types.md) explains why types can mention values. [Tactics](./14_tactics.md) and [Proof Strategy](./13_proof_strategy.md) cover how to actually get proofs done. [Artificial Intelligence](./19_artificial_intelligence.md) discusses where this is heading.
