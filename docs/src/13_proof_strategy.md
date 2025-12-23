# Proof Strategy

The previous articles taught you individual tactics. Now we learn how to think. A proof is not a random sequence of tactics that happens to work. It is a structured argument, and understanding that structure makes the difference between flailing and fluency. The gap between knowing the tactics and knowing how to prove things is the gap between knowing the rules of chess and knowing how to not lose immediately.

## The Goal State

Every proof begins with a goal and ends with no goals. The goal state is your map. Learning to read it fluently is the most important skill in tactic-based proving.

```
case succ
n : Nat
ih : P n
⊢ P (n + 1)
```

This goal state tells you everything: you are in the `succ` case of an induction, you have a natural number `n`, you have an induction hypothesis `ih` stating that $P(n)$ holds, and you must prove $P(n + 1)$. The turnstile $\vdash$ separates what you have from what you need.

When a proof has multiple goals, they appear stacked. The first goal is your current focus. Tactics typically operate on the first goal, though combinators like `all_goals` and `any_goals` can target multiple goals simultaneously.

## Goal State Evolution

Here is an induction proof showing how the goal state evolves at each step:

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:goal_state_example}}
```

## Categories of Tactics

Tactics fall into natural categories based on what they do to the goal state. Understanding these categories helps you choose the right tool.

**Introduction tactics** move structure from the goal into the context. When your goal is $P \to Q$, the tactic `intro h` assumes $P$ (calling it `h`) and changes the goal to $Q$. When your goal is $\forall x, P(x)$, the tactic `intro x` introduces a fresh $x$ and changes the goal to $P(x)$. Introduction tactics make progress by assuming what you need to prove under.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:introduction_tactics}}
```

**Elimination tactics** use structure from the context to transform the goal. When you have `h : P ∧ Q` and need $P$, the tactic `exact h.1` extracts the left component. When you have `h : P ∨ Q`, the tactic `cases h` splits into two goals, one assuming $P$ and one assuming $Q$. Elimination tactics make progress by using what you have.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:elimination_tactics}}
```

**Rewriting tactics** transform the goal using equalities. The tactic `rw [h]` replaces occurrences of the left side of `h` with the right side. The tactic `simp` applies many such rewrites automatically. Rewriting makes progress by simplifying toward something obviously true.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:rewriting_tactics}}
```

**Automation tactics** search for proofs. The tactic `simp` tries simplification lemmas. The tactic `omega` solves linear arithmetic. The tactic `aesop` performs general proof search. Automation makes progress by doing work you would rather not do by hand.

**Structural tactics** manipulate the proof state without making logical progress. The tactic `swap` reorders goals. The tactic `rename` changes hypothesis names. The tactic `clear` removes unused hypotheses. These tactics keep your proof organized.

## Reading the Goal

Before applying any tactic, ask: what is the shape of my goal? The outermost connective determines your next move.

Goals that require building structure call for introduction tactics. If your goal is an implication $P \to Q$, use `intro` to assume $P$ and reduce the goal to $Q$. Universal statements $\forall x, P(x)$ work the same way: `intro x` gives you an arbitrary $x$ and asks you to prove $P(x)$. For conjunctions $P \land Q$, use `constructor` to split into two subgoals. For disjunctions $P \lor Q$, you must commit: `left` obligates you to prove $P$, while `right` obligates you to prove $Q$. Existentials $\exists x, P(x)$ require a witness: `use t` provides the term $t$ and leaves you to prove $P(t)$.

Goals that are equations or basic facts call for different tactics. For equality $a = b$, try `rfl` if the terms are definitionally equal, `simp` for simplification, `rw` with known equalities, or `ring` for algebraic identities. Negation $\neg P$ is secretly an implication: since $\neg P$ means $P \to \bot$, you use `intro h` to assume $P$ and then derive a contradiction. If your goal is $\bot$ itself, you need to find conflicting hypotheses.

## Reading the Context

Your context contains hypotheses. Each one is a tool waiting to be used. The shape of a hypothesis determines what you can do with it.

Hypotheses that provide conditional information let you make progress when you can satisfy their conditions. An implication $h : P \to Q$ gives you $Q$ if you can prove $P$. When your goal is $Q$, use `apply h` to reduce it to proving $P$. A universal $h : \forall x, P(x)$ can be instantiated at any term: `specialize h t` replaces $h$ with $P(t)$, or `have ht := h t` keeps the original.

Hypotheses that package multiple facts can be taken apart. A conjunction $h : P \land Q$ gives you both pieces: access them with `h.1` and `h.2`, or destructure with `obtain ⟨hp, hq⟩ := h`. An existential $h : \exists x, P(x)$ packages a witness and a proof: `obtain ⟨x, hx⟩ := h` extracts both. A disjunction $h : P \lor Q$ requires case analysis since you do not know which side holds: `cases h` splits your proof into two branches.

An equality $h : a = b$ lets you substitute. Use `rw [h]` to replace $a$ with $b$ in your goal, or `rw [← h]` to go the other direction.

## Proof Patterns

Certain proof structures recur constantly. Recognizing them saves time.

**Direct proof**: Introduce assumptions, manipulate, conclude. Most proofs follow this pattern.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:direct_proof}}
```

**Proof by cases**: When you have a disjunction or an inductive type, split and prove each case.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:proof_by_cases}}
```

**Proof by induction**: For properties of recursive types, prove the base case and the inductive step.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:proof_by_induction}}
```

**Proof by contradiction**: Assume the negation and derive $\bot$.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:proof_by_contradiction}}
```

**Proof by contraposition**: To prove $P \to Q$, prove $\neg Q \to \neg P$ instead.

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:proof_by_contraposition}}
```

### Backward and Forward Reasoning

Backward reasoning works from goal toward hypotheses. Forward reasoning builds from hypotheses toward the goal:

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:backward_reasoning}}
```

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:forward_reasoning}}
```

### Induction Patterns

Induction is the workhorse for recursive types:

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:induction_patterns}}
```

### Case Splitting

When the path forward depends on which case holds:

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:case_splitting}}
```

### Proof by Contradiction

When direct proof fails, assume the negation and derive absurdity:

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:contradiction}}
```

### Choosing Automation

Different automation tactics excel at different domains:

```lean
{{#include ../../src/ZeroToQED/ProofStrategy.lean:automation_choice}}
```

## When You Get Stuck

Every proof hits obstacles. Here is how to get unstuck.

**Simplify first**. Try `simp` or `simp only [relevant_lemmas]`. Often the goal simplifies to something obvious.

**Check your hypotheses**. Do you have what you need? Use `have` to derive intermediate facts. Use `obtain` to destructure complex hypotheses.

**Try automation**. For arithmetic, try `omega` or `linarith`. For algebraic identities, try `ring` or `field_simp`. For general goals, try `aesop` or `decide`.

**Work backwards**. What would make your goal obviously true? If you need $P \land Q$, you need to prove both $P$ and $Q$. What tactics produce those subgoals?

**Work forwards**. What can you derive from your hypotheses? If you have $h : P \to Q$ and `hp : P`, you can derive $Q$.

**Split the problem**. Use `have` to state and prove intermediate lemmas. Breaking a proof into steps often reveals the path.

**Read the error**. Lean's error messages are verbose but precise. "Type mismatch" tells you what was expected and what you provided. "Unknown identifier" means a name is not in scope. "Unsolved goals" means you are not done.

**Use the library**. Mathlib contains thousands of lemmas. Use `exact?` to search for lemmas that close your goal. Use `apply?` to search for lemmas whose conclusion matches your goal.

## Tactic Composition

Tactics compose in several ways.

**Sequencing**: Separate tactics with newlines or semicolons. Each tactic operates on the result of the previous one.

```lean
theorem seq_demo (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  exact h.2
  exact h.1
```

**Focusing**: Use `·` to focus on a single goal. Indentation groups tactics under a focus.

```lean
theorem focus_demo (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1
```

**Combinators**: Use `<;>` to apply a tactic to all goals produced by the previous tactic. Use `first | t1 | t2` to try tactics in order. Use `repeat t` to apply a tactic until it fails.

```lean
theorem combinator_demo (P : Prop) (h : P) : P ∧ P ∧ P := by
  constructor <;> (try constructor) <;> exact h
```

## Next-Generation Automation

The tactics described so far require you to think. You read the goal, choose a strategy, apply tactics step by step. This is how mathematicians have always worked, and there is value in understanding your proof at every stage. But a new generation of tactics is changing the calculus of what is worth formalizing.

Higher-order tactics like `aesop`, `grind`, and SMT integration lift proof development from low-level term manipulation to structured, automated search over rich proof states. Instead of specifying every proof step, you specify goals, rule sets, or search parameters, and these tactics synthesize proof terms that Lean's kernel then checks. The soundness guarantee remains absolute since the kernel verifies everything, but the human cost drops dramatically. This decoupling of "what should be proved" from "how to construct the term" is what makes large-scale formalization feasible.

[`aesop`](https://github.com/leanprover-community/aesop) implements white-box best-first proof search, exploring a tree of proof states guided by user-configurable rules. Unlike black-box automation, `aesop` lets you understand and tune the search: rules are indexed via discrimination trees for rapid retrieval, and you can register domain-specific lemmas to teach it new tricks. [`grind`](https://lean-lang.org/blog/2024-12-6-grind/) draws inspiration from modern SMT solvers, maintaining a shared workspace where congruence closure, E-matching, and forward chaining cooperate on a goal. It excels when many interacting equalities and logical facts are present, automatically deriving consequences that would be tedious to script by hand. For goals requiring industrial-strength decision procedures, [SMT tactics](https://arxiv.org/pdf/2505.15796.pdf) send suitable fragments to proof-producing solvers like cvc5, then reconstruct proofs inside Lean so the kernel can verify them. This lets Lean leverage decades of solver engineering while preserving the LCF-style trust model where only the small kernel must be trusted.

The strategic question is when to reach for automation versus working by hand. The temptation is to try `grind` on everything and move on when it works. This is efficient but opaque: you learn nothing, and when automation fails on a similar goal later, you have no insight into why. A better approach is to use automation to explore, then understand what it found. Goals that would take an hour of tedious case analysis now take seconds. This frees you to tackle harder problems. But remember: when `grind` closes a goal, it has found a valid proof term. It has not gained insight. That remains your job.

## The Tactics Reference

The following article is a reference. It documents every major tactic in Lean 4 and Mathlib, organized alphabetically. You do not need to memorize it. You need to know it exists, and you need to know how to find the tactic you need.

When you encounter a goal you do not know how to prove, return here. Ask: what is the shape of my goal? What is in my context? What pattern does this proof follow? The answer will point you to the right tactic, and the reference will tell you how to use it.

The strategies in this article apply beyond Lean. The structure of mathematical argument is universal. Direct proof, case analysis, induction, contradiction: these are the fundamental patterns of reason itself. Learning them in a proof assistant merely makes them explicit. You cannot handwave past a case you forgot to consider when the computer is watching.
