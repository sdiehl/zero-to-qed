# Artificial Intelligence

In 2024, [a computer solved several problems](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) at the International Mathematical Olympiad with formally verified proofs. In 2025, [a system reached gold-medal standard](https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/). What makes these results worth noting is not that machines did well at competition math, but how: the proofs were checked down to the axioms, so the result holds whether or not you trust the system that produced it. That combination, a search procedure that can be wrong paired with a checker that cannot, is the subject of this chapter.

## The Current State

[Mathlib](https://github.com/leanprover-community/mathlib4) contains over two million lines of formalized mathematics spanning algebra, analysis, topology, and number theory, and it grows by thousands of theorems a month. No single person understands all of it, and none needs to: a theorem you formalize today can be imported and reused later without anyone rechecking your work, because the proof still typechecks. **Neural networks** now propose proof steps that formal systems then verify. The model guesses, the kernel checks. [DeepSeek-Prover](https://huggingface.co/collections/deepseek-ai/deepseek-prover) and [LeanDojo](https://leandojo.org/) make this workflow available today, and projects like [PhysLean](https://github.com/HEPLean/PhysLean) are extending it beyond pure mathematics to Maxwell's equations, quantum mechanics, and field theory.

The limits are real. Higher-order logic is undecidable; [Church and Turing](https://en.wikipedia.org/wiki/Entscheidungsproblem) settled that in 1936, so there is no general procedure that decides every statement. Formalization is also expensive: the Polynomial Freiman-Ruzsa conjecture took roughly 20,000 lines of Lean for a 50-page paper. Some informal mathematics resists formalization because it leans on intuition a checker cannot share. What you get in exchange, within the scope you can formalize, is a different kind of guarantee from testing: the proof typechecks or it does not.

## Why It Matters

Two kinds of organization fund this work. Research foundations support theorem provers as infrastructure for mathematics. Companies that ship correctness-critical software support them because ordinary testing leaves gaps they cannot afford. [Knight Capital](https://en.wikipedia.org/wiki/Knight_Capital_Group) lost \$440 million in 45 minutes to a deployment bug: the code did exactly what it was written to do, but what it was written to do was wrong. Formal methods addresses both halves of that failure. It checks that the code matches the specification, and it forces the specification to be precise enough to check in the first place. The second half is often the more useful one, since writing a specification you can actually prove tends to expose the parts of a problem you did not fully understand.

## The Prover-Verifier Architecture

The idea behind systems like [DeepSeek-Prover-V2](https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-671B) is to wrap a neural network in a loop where a formal system acts as judge.

The pipeline is roughly this. A large model decomposes a theorem into lemmas. A smaller specialized model attempts to prove each lemma in Lean. The Lean compiler checks the result. If it fails, the model retries with the error message as feedback; if it passes, the lemma is settled. The system then assembles the proven lemmas into a complete proof.

This setup limits the hallucination problem in formal domains. In standard RLHF, humans grade answers, which is noisy and expensive. In a prover-verifier loop the compiler supplies a binary signal instead, which makes reinforcement learning straightforward to set up. [DeepSeek-R1-Zero](https://arxiv.org/abs/2501.12948) learned to reason without supervised fine-tuning, picking up self-correction behaviors from trial and error against the verifier.

The same signal supports a data loop. DeepSeek generated large numbers of formal statements, verified them with Lean, and fed the correct proofs back into training, with no human annotation. Better provers produce more verified training data, which in turn trains better provers, though how far this loop runs before returns level off is not yet known.

Search strategy matters here. [DeepSeek-Prover-V2](https://arxiv.org/abs/2408.08152) uses [Monte Carlo Tree Search](https://en.wikipedia.org/wiki/Monte_Carlo_tree_search) to explore proof paths and backtrack from dead ends, the same family of method as [AlphaGo](https://deepmind.google/technologies/alphago/), but evaluating partial proof states instead of board positions.

A related idea is **inference-time scaling**: rather than only making models bigger at training time, let them spend more computation at inference time by reasoning for more tokens. On some benchmarks this improves accuracy. Whether it keeps paying off or hits diminishing returns is an open empirical question, and the answer probably differs by domain.

## Modern Reasoning Models

Recent models have grown more capable at writing Lean. The current generation, [Claude Opus 4.7](https://www.galois.com/articles/claude-can-sometimes-prove-it), Gemini 3 Pro with Deep Think, and the GPT-5 series, can complete non-trivial proofs with guidance, where the same model families a year earlier struggled with basic tactics. None of them is an autonomous mathematician; they are useful collaborators for parts of the work. Treat the specific model name as a moving target. What matters for this chapter is the workflow, which transfers across whichever model is current.

The key to effective AI-assisted theorem proving is giving models access to the proof state. Without it, they generate tactics blind and hallucinate lemma names. With it, they can read the goal, search for relevant theorems, and build proofs interactively. The **[Model Context Protocol](https://modelcontextprotocol.io/)** standardizes this interaction, letting AI assistants query external tools through a common interface.

### The ML Infrastructure Stack

Progress in neural theorem proving is measured against standardized benchmarks. [MiniF2F](https://github.com/openai/miniF2F) contains 488 Olympiad-level problems (IMO, AIME, AMC) formalized across multiple proof assistants; the strongest systems report numbers above 90% under generous Pass@N, so it now functions more as a floor than a frontier. [PutnamBench](https://trishullab.github.io/PutnamBench/) offers 1724 substantially harder problems from the Putnam competition, where systems reach the double digits but the long tail remains difficult. [ProofNet](https://github.com/zhangir-azerbayev/ProofNet) covers 371 undergraduate textbook exercises. Models are scored with `Pass@N`: generate N attempts, count success if any one verifies. Higher N (32, 128, 512) measures coverage; `Pass@1` measures single-shot accuracy. The two can differ a lot, so it is worth checking which N a reported number uses before comparing systems.

[LeanDojo](https://leandojo.org/) wraps Lean 4 in a Python API, turning theorem proving into a reinforcement-learning environment: you send a tactic, it returns success or an error message. This is the bridge between neural networks and the Lean kernel, and much of the research in this area builds on it.

[Lean Copilot](https://github.com/lean-dojo/LeanCopilot) brings the same idea into VS Code, suggesting tactics as you write proofs using a local or remote LLM. When you accept a suggestion, Lean verifies it. The model fills in routine steps; you supply the direction.

[llmstep](https://github.com/wellecks/llmstep) is a lighter-weight, model-agnostic alternative that calls an LLM to suggest the next proof step and works with any backend.

You can assemble a complete prover-verifier loop today: a current reasoning model (Claude Opus, Gemini Pro, GPT, or an open-weights model like DeepSeek-Prover) as the prover, LeanDojo as the environment, and Lean as the verifier. Prompt the model with the goal state, take its tactic, check it with Lean, feed any error back as context, and repeat. In practice the exact model matters less than the loop around it: a mid-tier model with good error feedback often outperforms a stronger model running without access to the proof state.

### Setting Up Claude Code

[Claude Code](https://docs.anthropic.com/en/docs/claude-code) is Anthropic's command-line tool for AI-assisted development. To use it with Lean, you need to connect it to Lean's language server via MCP. First, ensure you have the [uv](https://github.com/astral-sh/uv) package manager installed. Then, from your Lean project root (after running `lake exe cache get` and `lake build`), register the MCP server:

```bash
claude mcp add lean-lsp uvx lean-lsp-mcp
```

This installs the [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) server, which exposes Lean's language server to Claude. The model can now read diagnostics, inspect goal states, query hover documentation, and search Mathlib using Loogle and LeanSearch. For project-scoped configuration that ships with the repo (so collaborators get the same setup), commit a `.mcp.json` at the root:

```json
{ "mcpServers": { "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] } } }
```

For richer automation, you can install the [lean4-skills](https://github.com/cameronfreer/lean4-skills) plugin, which provides structured workflows for common theorem proving tasks:

```bash
/plugin marketplace add cameronfreer/lean4-skills
```

The plugin adds specialized agents for proof optimization, sorry filling, axiom checking, and compiler-guided repair. These encode patterns that experienced Lean users tend to apply by hand, which can save time on routine tasks and make those patterns easier to discover when you are starting out.

### Setting Up Cursor and VS Code

For Cursor or VS Code with an MCP-compatible extension, add the server to your MCP settings:

```json
{ "mcpServers": { "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] } } }
```

The workflow is the same: the model reads proof states through the language server and proposes tactics for the current goal, and you review, accept or reject, and guide the search.

## What Comes Next

The pairing of neural search with formal verification has one property that distinguishes it from most uses of machine learning: the verifier is exact. A proof typechecks or it does not, so a convincing-but-wrong answer cannot slip through unnoticed. That binary signal is what lets these systems train against their own output, and it is a plausible reason formal domains may be among the first places automated reasoning becomes routinely useful. As provers improve and libraries like Mathlib grow, more of the routine work in a proof can reasonably be handed off, though the hard parts still need a person who understands the problem.

The tooling also tends to transfer. A proof-automation library written for one problem is often usable for others, from compilers and distributed protocols to cryptographic primitives, and much of the underlying infrastructure is open source, so progress in one group is built on by another.

How far this goes is genuinely uncertain. It is possible that automated reasoning becomes a standard part of how serious software and mathematics are checked; it is also possible that progress slows once the easy benchmarks are saturated. The honest summary is that the direction is promising and the ceiling is unknown, which is reason enough to learn the tools rather than to make predictions about them.

## Conclusion

If you are reading this as a student or someone early in your career, this work is worth trying. Watching a proof come together, seeing the goal state shrink to nothing, getting the green checkmark from the compiler when it finally clicks: it is like solving puzzles, except the puzzles are deep and the solutions do not expire. A theorem you formalize stays valid indefinitely, which is an unusual thing to be able to say about a piece of work. The field is still small enough that careful work can make a real contribution.

It is also hard, and the learning curve is real. There will be days when nothing closes and the goal state seems to mock you. That is normal. The way through is the same as for any proof: one lemma at a time.

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

- [DeepSeek-Prover-V2-671B](https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-671B): 671B parameter model built on DeepSeek-V3-Base, the open-weights baseline for serious neural theorem proving. The V2 paper reported 88.9% on MiniF2F-test using recursive subgoal decomposition and RL with binary verification feedback; subsequent open-source efforts have pushed numbers higher
- [DeepSeek-Prover-V1.5](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5): Prover-verifier codebase
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
