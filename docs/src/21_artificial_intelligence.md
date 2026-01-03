# Artificial Intelligence

In 2024, [a computer solved one of the hardest problems](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) at the International Mathematical Olympiad with a formally verified proof. In 2025, [another hit gold-medal standard](https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/). The proofs were checked down to the axioms. No trust required. The interesting part is not that machines beat humans at competition math. The interesting part is that reason is becoming executable at scale, and that will change the world. How quickly is an open question.

[Mathlib](https://github.com/leanprover-community/mathlib4) now contains 1.9 million lines of formalized mathematics spanning algebra, analysis, topology, and number theory. It grows by thousands of theorems monthly. No single person understands all of it, and no single person needs to. The theorem you formalize today may be imported by a researcher fifty years from now working on problems we cannot imagine. The proof will still check. Meanwhile, **neural networks** have learned to propose proof steps that formal systems verify. The model guesses, the kernel checks. [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover) and [LeanDojo](https://leandojo.org/) make this practical today. [PhysLean](https://github.com/HEPLean/PhysLean) is formalizing physics itself: Maxwell's equations, quantum mechanics, field theory. The tooling has matured faster than most expected.

We should be honest about limits. Higher-order logic is undecidable. [Church and Turing](https://en.wikipedia.org/wiki/Entscheidungsproblem) settled this in 1936. Formalization is expensive: the Polynomial Freiman-Ruzsa conjecture required 20,000 lines of Lean for a 50-page paper. Some domains resist entirely. Physics says "for large N" and expects you to understand. But within scope, something remarkable becomes possible: certainty. Not high confidence. Certainty. The proof typechecks or it does not.

This kind of work gets funded because it pushes the frontiers of human knowledge. Science foundations fund theorem provers because they see infrastructure for the future of mathematics. Trading firms fund them because they need systems that actually work. Both are right. [Knight Capital](https://en.wikipedia.org/wiki/Knight_Capital_Group) lost \$440 million in 45 minutes from a deployment bug. The code did exactly what it was written to do. It was simply written wrong. Formal methods addresses both failure modes: it verifies that the code matches the specification, and forces you to make the specification precise enough to verify. You cannot prove a theorem you do not understand. For firms whose existence depends on algorithm correctness, this discipline can be existential.

This is where it gets interesting, at least if you find the intersection of mechanism design, game theory, and formal methods interesting, which you should, because it is genuinely one of the most exciting open problems in theoretical computer science and also immediately practical. Markets are mathematical objects. **[Combinatorial auctions](https://www.onechronos.com/documentation/expressive/)**, where bidders express preferences over bundles of assets rather than individual items, turn resource allocation into constraint satisfaction problems. (See the [open problem](#open-problem-honesty-as-strategy) below for a concrete challenge in this domain.) This kind of problem reduces to [weighted set packing](https://en.wikipedia.org/wiki/Set_packing): find the best non-overlapping selection from exponentially many candidates. NP-hard in general, but tractable instances exist, and the boundary between hard and easy is where the interesting mathematics lives. Proving properties about these systems, that they are **incentive-compatible**, that they converge, that they allocate efficiently under stated assumptions, is exactly the kind of hard problem where clever types and formal verification shines. Every improvement in market mechanism design, every formally verified property of an auction protocol, translates into real systems allocating real resources. Better reasoning about markets means systems that allocate capital more efficiently, and efficient allocation is the difference between prosperity and stagnation.

The functional programming shops of Wall Street, the quant firms in New York and London, the AI labs in China, all contribute to this ecosystem. DeepSeek's open-source theorem provers emerged from it. The competition is global but the infrastructure is shared. A trading firm in New York open-sources a proof automation library; researchers in Beijing build on it. An AI lab in Hangzhou releases trained models; mathematicians in Paris use them. Private incentive aligns with public good. The tools developed for trading algorithms can verify medical devices. The techniques refined for financial models can prove properties of cryptographic protocols. And as AI infrastructure itself becomes tradeable, as markets emerge for GPU compute ([The AI Boom Needs a Market for Compute](https://www.bloomberg.com/news/articles/2025-09-26/the-ai-boom-needs-a-market-for-compute-just-like-oil-and-spectrum)), data center capacity, and model inference, the same auction theory applies. The resources that train the models are allocated by the mechanisms the models might one day verify. This is a brave new world of software and economics.

This is the future. AI agents will increasingly act in markets: trading, lending, allocating, optimizing. This is already happening. The question is not whether but how. An AI agent can be constrained by rules, but only if those rules are precise enough to check. Natural language policies are suggestions. Formally verified constraints are guarantees. Imagine market infrastructure where agents must prove, before executing, that their actions satisfy regulatory constraints, risk limits, fairness properties, and eventually machine-checkable proofs of Pareto efficiency of market mechanisms. This is a big, hairy, ambitious goal. Not "we reviewed the code" but "the system verified the proof." The agent that cannot demonstrate compliance cannot act. Formal constraints are not a limitation on AI autonomy. They can be the tools that make AI autonomy safe.

We are building that infrastructure now, whether we recognize it or not. Every verified auction protocol, every theorem about market equilibria, becomes a potential constraint on future autonomous systems. AI agents in markets are not a hypothetical. They are here, and more are coming. The practical question is not whether to allow them but how to make them work well. Formal verification offers something concrete: constraints that actually constrain, rules that cannot be silently violated, guarantees that hold regardless of what the model learned. Skip the existential risk debates. The point is engineering systems that do what they are supposed to do.

If you are reading this as a student or someone early in your career: this stuff is fun. Watching a proof come together, seeing the goal state shrink to nothing, getting that green checkmark from the compiler when everything finally clicks. It is like solving puzzles, except the puzzles are deep and the solutions last. The theorems you formalize will still be valid when you are gone. That is a strange thing to be able to say about your work. The field is small enough that you can make real contributions and growing fast enough that there is plenty to do.

The work is hard. The learning curve is real. There will be days when the goal state mocks you and nothing seems to work. This is normal. The difficulty is not a bug; it is the cost of building things that matter. Scientists have always endured frustration because progress depends on it. The stoic response is not to complain but to continue: one lemma at a time, one proof at a time, one small piece of certainty added to the edifice. The edifice grows. It has been growing for centuries, and you can be part of it.

Jump in.

---

## The Prover-Verifier Architecture

The breakthrough behind systems like [DeepSeek-Prover](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5) is architectural, not just scale. The key insight: wrap a neural network in a recursive loop where a formal system acts as judge.

The pipeline works as follows. A large model decomposes a theorem into lemmas. A smaller specialized model attempts to prove each lemma in Lean. The Lean compiler checks the proof. If it fails, the model retries with the error message as feedback. If it passes, the lemma is proven with certainty. The system synthesizes proven lemmas into a complete proof.

This architecture solves the hallucination problem for formal domains. In standard RLHF, humans grade answers, which is noisy and expensive. In prover-verifier loops, the compiler provides a binary signal: the proof typechecks or it does not. This enables pure reinforcement learning. [DeepSeek-R1-Zero](https://arxiv.org/abs/2501.12948) learned to reason without any supervised fine-tuning, developing self-correction behaviors purely from trial and error against a verifier. The model discovered "aha moments" on its own.

The synthetic data flywheel accelerates this. DeepSeek generated millions of formal statements, verified them with Lean, and fed the correct proofs back into training. No human annotation required. The loop is self-reinforcing: better provers generate more training data, which trains better provers.

The search strategy matters. [DeepSeek-Prover-V2](https://arxiv.org/abs/2408.08152) uses [Monte Carlo Tree Search](https://en.wikipedia.org/wiki/Monte_Carlo_tree_search) to explore proof paths, backtracking when a path fails. This is the same algorithmic family as [AlphaGo](https://deepmind.google/technologies/alphago/), applied to theorem proving. Instead of evaluating board positions, the model evaluates partial proof states.

The broader hypothesis is **inference-time scaling**: rather than making models bigger (training-time compute), make them think longer (inference-time compute). Early results suggest that letting models reason for more tokens improves accuracy, at least on certain benchmarks. But the upper bound on this improvement remains an open question. Whether inference-time scaling continues to yield gains, or hits diminishing returns at some threshold, is something the next generation of models will determine empirically. Test-time search, parallel rollouts, and recursive self-correction all bet on this dynamic. The bet may pay off. It may not.

---

## Open Problem: Honesty as Strategy

William Vickrey won the 1996 Nobel Prize in Economics for a deceptively simple idea. In an auction where the highest bidder wins but pays only the second-highest bid, lying about your value cannot help you. Truthful bidding is weakly dominant. This is not a conjecture or an empirical regularity. It is a theorem, provable from first principles.

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_types}}
```

The payoff structure captures the essence: you win if you outbid, but you pay what your opponent bid, not what you bid. Your bid determines whether you win. It does not determine what you pay.

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_clear}}
```

We can already prove that honesty never loses money:

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_safety}}
```

The deeper theorem is that honesty is optimal. No strategic deviation improves your expected outcome:

```lean
{{#include ../../src/ZeroToQED/Auction.lean:auction_open}}
```

[Fill in the sorry.](https://github.com/sdiehl/zero-to-qed/blob/main/src/ZeroToQED/Auction.lean) The proof is case analysis. Overbidding makes you win auctions you should lose, paying more than the item is worth. Underbidding makes you lose auctions you should win, missing profitable trades. Truthful bidding threads the needle: you win exactly when winning is profitable.

This two-bidder result is a toy, but the insight scales. [Combinatorial auctions](https://www.onechronos.com/documentation/expressive/) let participants bid on bundles of assets, expressing preferences like "I want A and B together, or neither." The optimization becomes NP-hard, but the incentive properties generalize. The [VCG mechanism](https://en.wikipedia.org/wiki/Vickrey%E2%80%93Clarke%E2%80%93Groves_mechanism) extends Vickrey's insight to arbitrary allocation problems. Markets that allocate spectrum, landing slots, and financial instruments all descend from these ideas.

[OneChronos](https://www.onechronos.com/) builds this infrastructure for financial markets. We run combinatorial auctions that match complex orders across multiple securities simultaneously. The theorems matter because they guarantee properties that no amount of testing could verify: incentive compatibility, efficiency under stated assumptions, bounds on strategic manipulation. These are hard problems at the intersection of optimization, game theory, and formal methods. If that sounds interesting, [we are hiring](https://www.onechronos.com/careers/).

---

## Modern Reasoning Models

Frontier models have become increasingly capable at writing Lean. As of December 2025, Gemini 3.5 Pro and [Claude Opus 4.5](https://www.galois.com/articles/claude-can-sometimes-prove-it) represent the state of the art for interactive theorem proving. Google reportedly has internal models that perform even better. Six months ago these models struggled with basic tactics; now they can complete non-trivial proofs with guidance. They are not yet autonomous mathematicians, but they are useful collaborators today.

The key to effective AI-assisted theorem proving is giving models access to the proof state. Without it, they generate tactics blind and hallucinate lemma names. With it, they can read the goal, search for relevant theorems, and build proofs interactively. The **[Model Context Protocol](https://modelcontextprotocol.io/)** standardizes this interaction, letting AI assistants query external tools through a common interface.

### The ML Infrastructure Stack

[LeanDojo](https://leandojo.org/) is the foundation. It wraps Lean 4 in a Python API, turning theorem proving into an RL environment. You send a tactic; it returns success or an error message. This is the bridge between neural networks and formal verification. Every serious research project in this space builds on it.

[Lean Copilot](https://github.com/lean-dojo/LeanCopilot) brings this into VS Code. It suggests tactics in real-time as you write proofs, using a local or remote LLM. When you accept a suggestion, Lean immediately verifies it. The human provides high-level guidance; the model fills in tedious proof steps. This collaboration is more productive than either working alone.

[llmstep](https://github.com/wellecks/llmstep) is a lightweight alternative, model-agnostic and easy to integrate. It calls an LLM to suggest the next proof step, designed to work with any backend.

You can build a complete prover-verifier loop today without proprietary models. Use Claude or GPT-4o as the prover, LeanDojo as the environment, and Lean as the verifier. The stack: prompt the model with the goal state, receive a tactic, check it with Lean, feed errors back as context, repeat. This gives you the reasoning power of frontier models with the guarantees of formal verification.

### Setting Up Claude Code

[Claude Code](https://docs.anthropic.com/en/docs/claude-code) is Anthropic's command-line tool for AI-assisted development. To use it with Lean, you need to connect it to Lean's language server via MCP. First, ensure you have the [uv](https://github.com/astral-sh/uv) package manager installed. Then, from your Lean project root (after running `lake build`), register the MCP server:

```bash
claude mcp add lean-lsp uvx lean-lsp-mcp
```

This installs the [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) server, which exposes Lean's language server to Claude. The model can now read diagnostics, inspect goal states, query hover documentation, and search Mathlib using Loogle and LeanSearch.

For richer automation, you can install the [lean4-skills](https://github.com/cameronfreer/lean4-skills) plugin, which provides structured workflows for common theorem proving tasks:

```bash
/plugin marketplace add cameronfreer/lean4-skills
```

The plugin adds specialized agents for proof optimization, sorry filling, axiom checking, and compiler-guided repair. These are not magic; they encode patterns that experienced Lean users apply manually. But they save time on routine tasks and help beginners discover effective strategies.

### Setting Up Cursor and VS Code

For Cursor or VS Code with an MCP-compatible extension, add the server to your MCP settings:

```json
{ "mcpServers": { "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] } } }
```

The workflow is similar: the model reads proof states through the language server and proposes tactics based on the current goal. The human reviews, accepts or rejects, and guides the search. This collaboration is more productive than either working alone.

---

## Resources

**Libraries & Tools**

- [Mathlib](https://github.com/leanprover-community/mathlib4): The formalized mathematics library
- [PhysLean](https://github.com/HEPLean/PhysLean): Formalizing physics in Lean
- [LeanDojo](https://leandojo.org/): ML infrastructure for theorem proving
- [Lean Copilot](https://github.com/lean-dojo/LeanCopilot): Neural inference in Lean
- [llmstep](https://github.com/wellecks/llmstep): Lightweight model-agnostic tactic suggestion
- [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp): MCP server for Lean interaction
- [LeanExplore](https://leanexplore.com/): Semantic search across Mathlib

**Models & Reproductions**

- [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover): Open-weight theorem proving models
- [DeepSeek-Prover-V1.5](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5): Official prover-verifier codebase
- [DeepSeek-R1](https://github.com/deepseek-ai/DeepSeek-R1): Reasoning model weights and documentation
- [TinyZero](https://github.com/Jiayi-Pan/TinyZero): Minimal reproduction of DeepSeek-R1-Zero reasoning
- [Open-R1](https://github.com/huggingface/open-r1): HuggingFace's open reproduction of the R1 pipeline
- [Verifiers](https://github.com/PrimeIntellect-ai/verifiers): Modular MCTS and search for LLM reasoning

**Papers & Analysis**

- [DeepSeek-R1: Incentivizing Reasoning Capability in LLMs](https://arxiv.org/abs/2501.12948): The R1-Zero paper on pure RL reasoning
- [DeepSeek-Prover-V2](https://arxiv.org/abs/2408.08152): Formal theorem proving with tree search
- [Process-Driven Autoformalization (FormL4)](https://arxiv.org/abs/2406.01940): Compiler-guided natural language to Lean translation
- [AI and Formal Verification](https://martin.kleppmann.com/2025/12/08/ai-formal-verification.html): Kleppmann on the convergence of LLMs and proof assistants
- [Technical Deep Dive: DeepSeek](https://magazine.sebastianraschka.com/p/technical-deepseek): Raschka's architectural analysis
