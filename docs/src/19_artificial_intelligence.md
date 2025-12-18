# Artificial Intelligence

In 2024, a computer solved one of the hardest problems at the International Mathematical Olympiad with a formally verified proof. In 2025, another hit gold-medal standard. The proofs were checked down to the axioms. No trust required. The interesting part is not that machines beat humans at competition math. The interesting part is that reason is becoming executable at scale, and that changes everything.

[Mathlib](https://github.com/leanprover-community/mathlib4) now contains 1.9 million lines of formalized mathematics spanning algebra, analysis, topology, and number theory. It grows by thousands of theorems monthly. No single person understands all of it, and no single person needs to. The theorem you formalize today may be imported by a researcher fifty years from now working on problems we cannot imagine. The proof will still check. Meanwhile, neural networks have learned to propose proof steps that formal systems verify. The model guesses, the kernel checks. [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover) and [LeanDojo](https://leandojo.org/) make this practical today. [PhysLean](https://github.com/HEPLean/PhysLean) is formalizing physics itself: Maxwell's equations, quantum mechanics, field theory. The tooling has matured faster than most expected.

We should be honest about limits. Higher-order logic is undecidable. [Church and Turing](https://en.wikipedia.org/wiki/Entscheidungsproblem) settled this in 1936. Formalization is expensive: the Polynomial Freiman-Ruzsa conjecture required 20,000 lines of Lean for a 50-page paper. Some domains resist entirely. Physics says "for large N" and expects you to understand. But within scope, something remarkable becomes possible: certainty. Not high confidence. Certainty. The proof typechecks or it does not. [seL4](https://en.wikipedia.org/wiki/L4_microkernel_family#High_assurance:_seL4) runs in critical systems with mathematical proof it cannot crash. [CompCert](https://en.wikipedia.org/wiki/CompCert) compiles C with proof the assembly matches the source. These are not research toys. They are deployed in critical infrastructure.

This work gets funded because it pushes the frontiers of human knowledge. Science foundations fund theorem provers because they see infrastructure for the future of mathematics. Trading firms fund them because they need systems that actually work. Both are right. Knight Capital lost $440 million in 45 minutes from a deployment bug. The code did exactly what it was written to do. It was simply written wrong. For firms whose existence depends on algorithm correctness, formal methods are existential.

This is where it gets interesting, at least if you find the intersection of mechanism design, game theory, and formal methods interesting, which you should, because it is genuinely one of the most exciting open problems in theoretical computer science and also immediately practical. Markets are mathematical objects. [Combinatorial auctions](https://www.onechronos.com/documentation/expressive/), where bidders express preferences over bundles rather than individual items, turn resource allocation into constraint satisfaction problems. (Shameless plug: [OneChronos](https://www.onechronos.com/) builds these for financial markets, and if you are the kind of person who reads articles like this for fun, [we should talk](https://www.onechronos.com/careers/).) The winner determination problem reduces to [weighted set packing](https://en.wikipedia.org/wiki/Set_packing): find the best non-overlapping selection from exponentially many candidates. NP-hard in general, but tractable instances exist, and the boundary between hard and easy is where the interesting mathematics lives. Proving properties about these systems, that they are incentive-compatible, that they converge, that they allocate efficiently under stated assumptions, is exactly the kind of problem where formal verification shines. Every improvement in market mechanism design, every formally verified property of an auction protocol, translates into real systems allocating real resources. Better reasoning about markets means systems that allocate capital more efficiently, and efficient allocation is the difference between prosperity and stagnation.

The functional programming shops of Wall Street, the quant firms in London and Hong Kong, the AI labs in China, all contribute to this ecosystem. DeepSeek's open-source theorem provers emerged from it. The competition is global but the infrastructure is shared. A trading firm in New York open-sources a proof automation library; researchers in Beijing build on it. An AI lab in Hangzhou releases trained models; mathematicians in Paris use them. Private incentive aligns with public good. The tools developed for trading algorithms can verify medical devices. The techniques refined for financial models can prove properties of cryptographic protocols. And as AI infrastructure itself becomes tradeable, as markets emerge for GPU compute, data center capacity, and model inference, the same auction theory applies. The resources that train the models are allocated by the mechanisms the models might one day verify.

There is a future taking shape. AI agents will increasingly act in markets: trading, lending, allocating, optimizing. This is already happening. The question is not whether but how. An AI agent can be constrained by rules, but only if those rules are precise enough to check. Natural language policies are suggestions. Formally verified constraints are guarantees. Imagine market infrastructure where agents must prove, before executing, that their actions satisfy regulatory constraints, risk limits, fairness properties. Not "we reviewed the code" but "the system verified the proof." The agent that cannot demonstrate compliance cannot act. Formal constraints are not a limitation on AI autonomy. They are the condition that makes AI autonomy safe.

We are building that infrastructure now, whether we recognize it or not. Every verified auction protocol, every theorem about market equilibria, becomes a potential constraint on future autonomous systems. AI agents in markets are not a hypothetical. They are here, and more are coming. The practical question is not whether to allow them but how to make them work well. Formal verification offers something concrete: constraints that actually constrain, rules that cannot be silently violated, guarantees that hold regardless of what the model learned. Skip the existential risk debates. The point is engineering systems that do what they are supposed to do.

If you are reading this as a student or someone early in your career: this stuff is fun. Watching a proof come together, seeing the goal state shrink to nothing, getting that green checkmark from the compiler when everything finally clicks. It is like solving puzzles, except the puzzles are deep and the solutions last. The theorems you formalize will still be valid when you are gone. That is a strange thing to be able to say about your work. The field is small enough that you can make real contributions and growing fast enough that there is plenty to do.

The work is hard. The learning curve is real. There will be days when the goal state mocks you and nothing seems to work. This is normal. The difficulty is not a bug; it is the cost of building things that matter. Scientists have always endured frustration because progress depends on it. The stoic response is not to complain but to continue: one lemma at a time, one proof at a time, one small piece of certainty added to the edifice. The edifice grows. It has been growing for centuries, and you can be part of it.

Jump in.

---

## Open Problem: Verified Auction Theory

Here is a concrete challenge. Markets move trillions of dollars daily on algorithms that have never been formally verified; proving properties about them is one of the few places where a theorem can be worth real money. The code below implements a combinatorial auction: participants submit orders expressing preferences over baskets of instruments, and the mechanism finds an allocation that maximizes welfare. Safety properties (no order executes worse than its limit) are tractable. The hard problem is proving **price improvement**: that participants get better execution than they could achieve through bilateral matching.

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_types}}
```

The mechanism finds welfare-maximizing allocations:

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_clear}}
```

Safety properties are provable:

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_safety}}
```

The open problem:

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_open}}
```

**The challenge**: [download the code](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Auction.lean) and fill in the `sorry`. Participants submit orders over baskets of securities; the mechanism finds a combinatorial match that clears simultaneously. The value proposition is price improvement: better execution than sequential bilateral matching. Directions you might take:

- **Prove price improvement bounds**. Define improvement as the difference between limit price and execution price. Prove that the allocation delivers non-negative improvement for all filled orders.
- **Verify the solver formulation**. Winner determination is solved via an optimization solver. Prove that feasible solutions correspond to valid allocations, and the objective maximizes welfare.
- **Characterize expressiveness gains**. Prove that basket preferences strictly improve outcomes: there exist order configurations where combinatorial matching achieves fills that no sequence of bilateral matches could.

Markets look like chaos but are actually mathematical objects with deep structure; proving theorems about them reveals invariants that no amount of testing could find. If you make on progress on this problem, we at [OneChronos](https://www.onechronos.com/) would love to hear from you. We build market infrastructure and work on these kinds of problems. There is a lot of non-trivial work involved, and we are always looking for smart people. Apply through [our careers page](https://www.onechronos.com/careers/) or [reach out to me](mailto:sdiehl@onechronos.com) directly.

---

## Resources

**Formalized Mathematics**
- [Mathlib](https://github.com/leanprover-community/mathlib4): The formalized mathematics library
- [PhysLean](https://github.com/HEPLean/PhysLean): Formalizing physics

**Neural Theorem Proving**
- [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover): Open-weight theorem proving models
- [LeanDojo](https://leandojo.org/): ML infrastructure for theorem proving
- [Lean Copilot](https://github.com/lean-dojo/LeanCopilot): Neural inference in Lean

**Interactive Proving with MCP**

The [Model Context Protocol](https://modelcontextprotocol.io/) standardizes how AI assistants interact with external tools. For theorem proving, this means LLMs can read goal states, query for relevant lemmas, and build proofs interactively rather than generating them blind. The [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) server exposes Lean's language server to AI agents, enabling access to diagnostics, goal states, hover documentation, and search tools like Loogle and LeanSearch.

> [!TIP]
> **Setup for Claude Code** (run in your Lean project root):
> ```bash
> claude mcp add lean-lsp uvx lean-lsp-mcp
> ```
> **Setup for Cursor/VS Code** (add to MCP settings):
> ```json
> { "mcpServers": { "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] } } }
> ```
> Requires [uv](https://github.com/astral-sh/uv) package manager. Run `lake build` before starting.

**Tools**
- [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp): MCP server for Lean interaction
- [LeanExplore](https://leanexplore.com/): Semantic search across Mathlib
