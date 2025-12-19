# Theorem Provers

_This article covers the history and landscape of theorem provers. If you do not care about context, skip to [Basics](./05_basics.md)._

The idea of mechanizing mathematical reasoning dates back centuries, but the modern era of theorem proving began in the 1960s and 1970s when researchers first attempted to implement formal logic on computers. These early systems were primitive by today's standards, but they established the fundamental insight that proofs could be represented as data structures and verified by algorithms.

## Early Systems

The first generation of theorem provers emerged from two distinct traditions. One tradition, exemplified by systems like [Automath](https://en.wikipedia.org/wiki/Automath) developed by Nicolaas de Bruijn in the late 1960s, focused on encoding existing mathematical proofs in a formal language that a computer could check. De Bruijn's work introduced many concepts that remain central to modern systems, including the idea that types could depend on values and that propositions could be represented as types. The other tradition focused on automated theorem proving, attempting to have computers discover proofs on their own through search procedures. While fully automated proving remains intractable for most interesting mathematics, techniques from this tradition inform the automation tactics available in modern proof assistants.

The 1980s saw the development of several influential systems. The Calculus of Constructions, introduced by Thierry Coquand and Gérard Huet, provided a unified foundation combining dependent types with a hierarchy of universes. This calculus became the theoretical basis for [Coq](https://en.wikipedia.org/wiki/Coq_(software)), which remains one of the most widely used proof assistants today. Coq pioneered many features now standard in the field, including tactic-based proof development, extraction of executable programs from proofs, and a module system for organizing large developments. Major verification efforts in Coq include the [CompCert](https://en.wikipedia.org/wiki/CompCert) certified C compiler and the mathematical proof of the [four color theorem](https://en.wikipedia.org/wiki/Four_color_theorem).

## The LCF Tradition

Around the same time, researchers in Edinburgh developed the LCF system and its descendants, which introduced the influential LCF architecture. In this design, there is a small trusted kernel that defines what constitutes a valid proof, and all proof construction must ultimately pass through this kernel. This approach provides strong guarantees because only the kernel needs to be trusted, while tactics and automation can be implemented in untrusted code. The [HOL family](https://en.wikipedia.org/wiki/HOL_(proof_assistant)) of provers, including HOL4 and Isabelle/HOL, descend from this tradition. [Isabelle](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant)) in particular has been used for major verification efforts including the [seL4](https://en.wikipedia.org/wiki/SeL4) verified operating system kernel.

## First-Order Theorem Proving

A parallel tradition built theorem provers on first-order logic rather than type theory. The [Boyer-Moore](https://en.wikipedia.org/wiki/Nqthm) family of provers, culminating in ACL2, used an untyped computational substrate based on Lisp with powerful automation heuristics for discovering proofs. ACL2 achieved notable industrial successes, including verification of AMD's floating-point division after the Pentium FDIV bug made hardware correctness suddenly interesting to executives.

Despite these successes, first-order theorem proving has not been widely adopted outside specialized industrial applications. First-order logic imposes an expressiveness ceiling that makes formalizing modern mathematics awkward. Without dependent types, you cannot easily express properties like "a vector of length n" or "a sorted list." These systems rely heavily on opaque automation heuristics rather than user-programmable tactics, which makes it harder to understand why proofs fail and how to fix them. Most importantly, there is no Curry-Howard correspondence linking proofs to programs, which means verified algorithms cannot be extracted into executable code.

The contrast is instructive. Type-theoretic systems grew ecosystems of thousands of users, million-line mathematical libraries, and active research communities. First-order provers remained specialized tools for specific classes of problems. The Curry-Howard insight that proofs are programs and types are propositions turned out to be generatively powerful in ways that first-order theorem proving was not. When you can express your specification, your implementation, and your correctness proof in the same language, each informs the others. This unity is what makes dependent type theory feel like mathematics rather than a checkbox.

## Dependent Type Theory

The development of Martin-Löf type theory in the 1970s and 1980s provided another foundational framework that influenced systems like [Agda](https://en.wikipedia.org/wiki/Agda_(programming_language)) and later [Idris](https://en.wikipedia.org/wiki/Idris_(programming_language)). Per Martin-Löf's intensional type theory emphasized the computational content of proofs and introduced identity types as a way to reason about equality. Agda, developed primarily at Chalmers University, implements a variant of this theory with sophisticated support for dependent pattern matching. Its syntax influenced Lean's design, and it remains popular for research in type theory and programming language semantics.

Idris took a different approach by prioritizing practical programming with dependent types rather than theorem proving per se. Idris demonstrated that dependent types could be integrated into a language designed for general-purpose programming, with features like implicit arguments and type-driven development making dependently typed code more accessible to working programmers. Many of these ergonomic innovations influenced Lean 4's design.

The 2010s brought renewed interest in the foundations of mathematics through homotopy type theory, which reinterprets types as spaces and equality as paths. This perspective, developed by Vladimir Voevodsky and others, led to new proof assistants like Cubical Agda that implement univalent foundations. While Lean does not natively support cubical type theory, the mathematical insights from this research have influenced how the community thinks about equality and transport.

## The Ecosystem Problem

Most theorem provers die the same death: they work, but nobody uses them. The software is correct, the theory is sound, the papers get cited, and then the maintainer graduates or retires and the codebase rots. This is not a failure of engineering. It is a failure of ecosystem.

A theorem prover without a library is a programming language without packages. You can write everything from scratch, but you will not. The activation energy is too high. Automath proved you could encode mathematics in the 1960s. [Mizar](https://en.wikipedia.org/wiki/Mizar_system) built a large library but with a syntax that looked like it was designed to repel newcomers. The Boyer-Moore provers achieved industrial success at AMD but never grew a community. Each system had technical merit. None achieved escape velocity.

The systems that thrive today share a common pattern: a killer application that proved the approach could work at scale. Coq had CompCert. Isabelle had seL4. These existence proofs mattered. When someone asked "can you build anything real?" there was an answer.

## Lean's Position

Lean emerged from this rich history. The first version was developed by Leonardo de Moura at Microsoft Research starting in 2013, with the goal of building a system suitable for both interactive theorem proving and automated reasoning. Lean 2 and Lean 3 refined the system and built a substantial mathematical library. Lean 4, shipped in 2021, was a ground-up rewrite with several things done right.

**Speed.** Lean 4 compiles to C and runs fast. Not "fast for a theorem prover" but actually fast. You can write command-line tools, build systems, even games. This matters because proof assistants are IDEs, and IDE responsiveness determines whether people finish their proofs or give up.

**Metaprogramming.** Lean 4's tactic framework is written in Lean itself. You can inspect it, modify it, and write your own tactics without learning a separate metalanguage. In Coq, the tactic language (Ltac) is a different beast from the term language. In Lean, tactics are just programs.

**Syntax.** Lean looks like a normal programming language. Functions are functions. Pattern matching works how you expect. Unicode is optional. Lower friction means more users.

**Mathlib.** At 1.9 million lines, [Mathlib](https://en.wikipedia.org/wiki/Mathlib) is the largest coherent mathematical library ever created. When people ask "can I formalize real mathematics?" the answer is: probably someone already did, go look it up. Mathlib covers undergraduate and graduate-level material across algebra, analysis, topology, number theory, and other areas. These libraries demonstrate that modern proof assistants can handle serious mathematics, not just toy examples.

**Community momentum.** Mathlib grows by thousands of theorems monthly. The [Lean Zulip](https://leanprover.zulipchat.com/) is active and welcoming. [Kevin Buzzard](https://www.imperial.ac.uk/people/k.buzzard) teaches undergraduates at Imperial. [Terence Tao](https://terrytao.wordpress.com/) formalizes his papers. When working mathematicians adopt your tool, the library grows faster.

**AI integration.** Lean is the default target for neural theorem proving research. [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover), [LeanDojo](https://leandojo.org/), and others chose Lean because the metaprogramming API makes tool integration tractable. This creates a flywheel: more AI tooling attracts more users attracts more AI tooling.

## The Modern Landscape

Today's theorem provers share many features despite their different foundations. Most support some form of dependent types, allowing types to depend on values and enabling precise specifications. Most provide tactic languages for interactive proof development alongside term-mode proof construction. Most include automation ranging from simple rewriting to sophisticated decision procedures.

The systems differ in their logical foundations, their approach to equality and computation, their support for classical versus constructive reasoning, and their emphasis on programming versus pure mathematics. Lean occupies a distinctive position by providing classical logic by default while maintaining strong computational properties, and by treating programming and proving as equally important activities.

Agda has elegant syntax and supports cubical type theory for people who care about homotopy, but has no substantial mathematical library. Idris pioneered practical dependent types for programming, but the community has not coalesced around a shared library. The HOL family uses simpler type theories without full dependent types, which makes automation easier but specifications harder. These systems have their niches but face the same ecosystem challenges that have always separated survivors from the graveyard.

## Getting Started

If you are starting today, Lean is a reasonable choice. The syntax is approachable, the tooling is modern, the library is substantial, and the community is active. The alternatives are not wrong, but the path is less well-trodden.

If you want the theoretical foundations: [Type Theory](./11_type_theory.md) covers the core calculus. [Dependent Types](./12_dependent_types.md) explains why types can mention values. [Tactics](./14_tactics.md) and [Proof Strategy](./13_proof_strategy.md) cover how to actually get proofs done. [Artificial Intelligence](./20_artificial_intelligence.md) discusses where this is heading.
