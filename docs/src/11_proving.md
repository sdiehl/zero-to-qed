# Proofs

You have written functions. You have defined types. You have pattern matched, recursed, and composed. But you have not yet proved anything.

The difference matters. When you write a function, the compiler checks that types align, but it does not verify that your code does what you claim. You say this function sorts? The compiler shrugs. In theorem proving, you make claims and then justify them. The compiler verifies that your justification actually establishes the claim. You cannot bluff your way through a proof.

A bear learns to fish by watching the stream, understanding where salmon pause, developing patience for the moment when motion becomes certainty. Proving is similar. You learn to read the goal state, understand where progress stalls, develop patience for the tactic that transforms confusion into clarity.

## Notation

Before we write our first proof, we need a shared language. The notation below bridges three worlds: the mathematical symbols you find in logic textbooks, the inference rules used in programming language theory (as in Pierce's [Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) and Harper's [Practical Foundations for Programming Languages](http://www.cs.cmu.edu/~rwh/pfpl/)), and the Lean syntax you will write. Learning to read all three simultaneously is the key to fluency.

| Symbol        | Name      | Meaning                             |
| ------------- | --------- | ----------------------------------- |
| $\vdash$  | turnstile | "proves" or "entails"               |
| $\Gamma$  | Gamma     | the context (hypotheses we can use) |
| $\to$     | arrow     | implication or function type        |
| $\forall$ | for all   | universal quantification            |
| $\exists$ | exists    | existential quantification          |
| $\land$   | and       | conjunction                         |
| $\lor$    | or        | disjunction                         |
| $\top$    | top       | truth (trivially provable)          |
| $\bot$    | bottom    | falsehood (unprovable)              |

A **judgment** $\Gamma \vdash P$ reads "from **context** $\Gamma$, we can prove $P$." An **inference rule** shows how to derive new judgments from existing ones:

\\[
\frac{\Gamma \vdash P \quad \Gamma \vdash Q}{\Gamma \vdash P \land Q} \text{(∧-intro)}
\\]

This rule says: if you can prove $P$ and you can prove $Q$, then you can prove $P \land Q$. The **premises** sit above the line; the **conclusion** below. The name on the right identifies the rule. Every tactic you learn corresponds to one or more such rules. The tactic is the mechanism; the rule is the justification.

## Tactics as Proof-State Transformers

You may have repressed the trauma of high school algebra, but the core idea was sound: you start with $2x + 5 = 11$ and apply operations until you reach $x = 3$. Subtract 5, divide by 2, each step transforming the equation into something simpler. The tedium was doing it by hand, error-prone and joyless. But the method itself, symbolic manipulation through mechanical transformation, turns out to be extraordinarily powerful when the machine handles the bookkeeping.

Tactics work the same way. You start with a **goal** (what you want to prove) and a context (what you already know). Each **tactic** transforms the goal into simpler **subgoals**. You keep applying tactics until no goals remain. The proof is the sequence of transformations, not a single flash of insight.

Think of it as a game. Your current position is the proof state: the facts you hold and the destination you seek. Each tactic is a legal move that changes your position. Some moves split one goal into two (like `constructor` creating two subgoals). Some moves close a goal entirely (like `rfl` finishing with a checkmate). You win when the board is empty.

Formally, a **proof state** is a judgment $\Gamma \vdash G$: context $\Gamma$, goal $G$. A tactic transforms one proof state into zero or more new proof states. When no goals remain, the proof is complete. This table is your Rosetta Stone:

| Tactic          | Before                                | After                                                           | Rule                                     |
| --------------- | ------------------------------------- | --------------------------------------------------------------- | ---------------------------------------- |
| `intro h`       | $\Gamma \vdash P \to Q$           | $\Gamma, h:P \vdash Q$                                      | $\to$-intro                          |
| `apply f`       | $\Gamma \vdash Q$                 | $\Gamma \vdash P$                                           | $\to$-elim (given $f : P \to Q$) |
| `exact h`       | $\Gamma, h:P \vdash P$            | $\square$                                                   | assumption                               |
| `rfl`           | $\Gamma \vdash t = t$             | $\square$                                                   | refl                                     |
| `constructor`   | $\Gamma \vdash P \land Q$         | $\Gamma \vdash P$, $\Gamma \vdash Q$                    | $\land$-intro                        |
| `left`          | $\Gamma \vdash P \lor Q$          | $\Gamma \vdash P$                                           | $\lor$-intro₁                        |
| `right`         | $\Gamma \vdash P \lor Q$          | $\Gamma \vdash Q$                                           | $\lor$-intro₂                        |
| `cases h`       | $\Gamma, h:P \lor Q \vdash R$     | $\Gamma, h:P \vdash R$, $\Gamma, h:Q \vdash R$          | $\lor$-elim                          |
| `induction n`   | $\Gamma \vdash \forall n.\, P(n)$ | $\Gamma \vdash P(0)$, $\Gamma, ih:P(k) \vdash P(k{+}1)$ | Nat-ind                                  |
| `rw [h]`        | $\Gamma, h: a=b \vdash P[a]$      | $\Gamma, h:a=b \vdash P[b]$                                 | subst                                    |
| `simp`          | $\Gamma \vdash G$                 | $\Gamma \vdash G'$                                          | rewrite*                                 |
| `contradiction` | $\Gamma, h:\bot \vdash P$         | $\square$                                                   | $\bot$-elim                          |

The symbol $\square$ marks a completed goal. Multiple goals after "After" mean the tactic created subgoals. Read left to right: you have the state on the left, you apply the tactic, you must now prove everything on the right. This is the algebra of proof. Each tactic is a function from proof states to proof states, and a complete proof is a composition that maps your theorem to $\square$.

If the table above looks like both logic and programming, that is not a coincidence.

## Proving vs Programming

The surprising insight is that proving and programming are the same activity viewed differently. A proof is a program. A theorem is a type. When you prove $P \to Q$, you are writing a function that transforms evidence for $P$ into evidence for $Q$. This correspondence, the **Curry-Howard isomorphism**, means that logic and computation are two views of the same underlying structure:

| Logic           | Programming              |
| --------------- | ------------------------ |
| **proposition** | type                     |
| **proof**       | program                  |
| $P \to Q$   | function from `P` to `Q` |
| $P \land Q$ | pair `(P, Q)`            |
| $P \lor Q$  | either `P` or `Q`        |
| $\top$      | unit type                |
| $\bot$      | empty type               |

Every function you have written so far was secretly a proof. Every proof you write from now on is secretly a program. Two cultures, mathematicians and programmers, spoke the same language for decades without knowing it.

## Your First Proof

Let us prove something undeniably true: one plus one equals two.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:first_proof}}
```

Whitehead and Russell famously required 362 pages of [Principia Mathematica](https://en.wikipedia.org/wiki/Principia_Mathematica) before reaching this result. We have done it in three characters. This is not because we are cleverer than Russell; it is because we inherited infrastructure. The Principia was an attempt to place all of mathematics on rigorous foundations, to banish the intuition and hand-waving that had allowed paradoxes to creep into set theory. It was a heroic, doomed effort: the notation was unreadable, the proofs were uncheckable by any human in finite time, and [Gödel would soon prove](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems) that the program could never fully succeed. But the ambition was right. The ambition was to make mathematics a science of proof rather than a craft of persuasion.

A century later, the ambition survives in different form. We do not write proofs in Russell's notation; we write them in languages that machines can check. The 362 pages compress to three characters not because the mathematics got simpler but because the verification got automated. What mathematicians have been writing all along was pseudocode: informal instructions meant for human execution, full of implicit steps and assumed context, correct only if the reader filled in the gaps charitably. We are finally compiling that pseudocode.

The keyword `by` enters tactic mode. Instead of writing a proof term directly, you give commands that build the proof incrementally. The tactic `rfl` (reflexivity) says "both sides of this equation compute to the same value, so they are equal." Lean evaluates `1 + 1`, gets `2`, sees that `2 = 2`, and accepts the proof. No faith required. No appeals to authority. The machine checked, and the machine does not lie.

Or does it? Ken Thompson's [Reflections on Trusting Trust](https://www.cs.cmu.edu/~rdriley/487/papers/Thompson_1984_ReflectionsonTrustingTrust.pdf) demonstrated that a compiler can be trojaned to insert backdoors into code it compiles, including into future versions of itself. Turtles all the way down. At some point you trust the hardware, the firmware, the operating system, the compiler that compiled your proof assistant. We choose to stop the regress somewhere, not because the regress ends but because we must act in the world despite uncertainty. This is the stoic's bargain: do the work carefully, verify what can be verified, and accept that perfection is not on offer. The alternative is paralysis, and paralysis builds nothing.

## The Goal State

When you write proofs in Lean, the editor shows you the current goal state. This is your map, your honest accounting of where you stand. Unlike tests that can pass while bugs lurk, unlike documentation that drifts from reality, the goal state cannot lie. It tells you exactly what you have (hypotheses) and exactly what you need to prove (the goal). The gap between aspiration and achievement is always visible.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:goal_state_demo}}
```

When you place your cursor after `by` in `add_zero`, you see:

```
n : Nat
⊢ n + 0 = n
```

The line `n : Nat` is your context: the facts you know, the tools you have. The symbol `⊢` (turnstile) separates what you have from what you need. The goal `n + 0 = n` is your obligation. After applying `rfl`, the goal disappears. No goals means the proof is complete. You have caught your fish.

## Reflexivity: `rfl`

The `rfl` tactic proves goals of the form $a = a$ where both sides are **definitionally equal**. In inference rule notation:

\\[
\frac{}{\Gamma \vdash a = a} \text{(refl)}
\\]

No premises above the line means the rule is an axiom: equality is reflexive, always, unconditionally. "Definitionally equal" means Lean can compute both sides to the same value without any lemmas. This is equality by computation, the most basic form of truth: run the program on both sides and see if you get the same answer.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:rfl_examples}}
```

When `rfl` works, it means the equality is "obvious" to Lean's computation engine. When it fails, you need other tactics to transform the goal into something `rfl` can handle.

## Triviality: `trivial`

The `trivial` tactic handles goals that are straightforwardly true. It combines several simple tactics and works well for basic logical facts.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:trivial_examples}}
```

## Simplification: `simp`

The `simp` tactic is your workhorse. It applies a database of hundreds of rewrite rules, accumulated over years by the mathlib community, to simplify the goal. This is collective knowledge made executable: every time someone proved that `x + 0 = x` or `list.reverse.reverse = list`, they added to the arsenal that `simp` deploys on your behalf.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:simp_examples}}
```

When `simp` alone does not suffice, you can give it additional lemmas: `simp [lemma1, lemma2]`. You can also tell it to use hypotheses from your context: `simp [h]`.

> [!TIP]
> When stuck, try `simp` first. It solves a surprising number of goals. If it does not solve the goal completely, look at what remains.

## Introducing Assumptions: `intro`

When your goal is an **implication** $P \to Q$, you assume $P$ and prove $Q$. This is the introduction rule for implication:

\\[
\frac{\Gamma, P \vdash Q}{\Gamma \vdash P \to Q} \text{(→-intro)}
\\]

The comma means "extended context": if you can prove $Q$ assuming $P$, then you can prove $P \to Q$ outright. The `intro` tactic performs this transformation, moving the antecedent from goal to hypothesis.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:intro_apply}}
```

After `intro hp`, the goal changes from `P → P` to just `P`, and you gain hypothesis `hp : P`. Multiple `intro` commands can be combined: `intro h1 h2 h3` introduces three assumptions at once.

## Applying Lemmas: `apply` and `exact`

The `apply` tactic uses the elimination rule for implication, also called **modus ponens**:

\\[
\frac{\Gamma \vdash P \to Q \quad \Gamma \vdash P}{\Gamma \vdash Q} \text{(→-elim)}
\\]

If you have a proof of $P \to Q$ and a proof of $P$, you can derive $Q$. When your goal is $Q$ and you `apply` a hypothesis $h : P \to Q$, Lean transforms your goal to $P$. The `exact` tactic says "this term is exactly what we need" and closes the goal.

In the `imp_trans` proof, `apply hqr` transforms the goal from `R` to `Q`, because `hqr : Q → R`. Then `apply hpq` transforms `Q` to `P`. Finally `exact hp` provides the `P` we need. Each step is modus ponens, chained backward.

## Intermediate Steps: `have`

Sometimes you want to prove a helper fact before using it. The `have` tactic introduces a new hypothesis with its own proof. This is how knowledge accumulates: you establish a stepping stone, name it, and build on it.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:have_example}}
```

The pattern `have name : type := proof` adds `name : type` to your context.

## Case Analysis: `cases`

When you have a value of an inductive type, `cases` splits the proof into one case per constructor. This is exhaustive reasoning: you consider every possible form the value could take, and you prove your claim holds in each. The compiler ensures you miss nothing. This is how careful decisions should be made: enumerate the possibilities, handle each one, leave no branch unexamined.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:cases_example}}
```

For `Bool`, there are two cases: `true` and `false`. For `Nat`, there are two cases: `zero` and `succ m`. For `Option`, there are `none` and `some n`.

## Induction

For properties of natural numbers, **mathematical induction** is the fundamental principle:

\\[
\frac{\Gamma \vdash P(0) \quad \Gamma, P(n) \vdash P(n+1)}{\Gamma \vdash \forall n.\, P(n)} \text{(Nat-ind)}
\\]

Prove the base case $P(0)$. Then prove the inductive step: assuming $P(n)$, show $P(n+1)$. From these two finite proofs, you derive a statement about infinitely many numbers. The `induction` tactic generates both proof obligations automatically. The principle dates to Pascal and Fermat, but the mechanization is new.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:induction_example}}
```

In the `succ` case, you get an induction hypothesis `ih` that assumes the property holds for `n`, and you must prove it holds for `n + 1`.

## Arithmetic: `omega`

For goals involving linear arithmetic over natural numbers or integers, `omega` is powerful. It implements a decision procedure for [Presburger arithmetic](https://en.wikipedia.org/wiki/Presburger_arithmetic), a fragment of number theory that is provably decidable. Within its domain, `omega` does not search or guess; it decides.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:omega_example}}
```

If your goal involves only addition, subtraction, multiplication by constants, and comparisons, try `omega`.

## Decision Procedures: `decide`

For decidable propositions, `decide` simply computes the answer. Is 7 less than 10? Run the comparison. Is this list empty? Check. Some questions have algorithms that answer them definitively, and `decide` invokes those algorithms. When it works, there is nothing to prove; the computation is the proof.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:decide_example}}
```

## Putting It Together

Real proofs combine multiple tactics. You introduce assumptions, simplify, split cases, apply lemmas, and close with computation. The art is knowing which tool fits which moment. With practice, patterns emerge: implications call for `intro`, equalities for `rw` or `simp`, inductive types for `cases` or `induction`. The goal state guides you.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:proof_workflow}}
```

```lean
{{#include ../../src/ZeroToQED/Proving.lean:combining_tactics}}
```

## The Tactics You Need

| Tactic      | Purpose                                                 |
| ----------- | ------------------------------------------------------- |
| `rfl`       | Prove `a = a` when both sides compute to the same value |
| `trivial`   | Prove obviously true goals                              |
| `simp`      | Simplify using rewrite rules                            |
| `intro`     | Assume hypotheses from implications and universals      |
| `apply`     | Use a lemma whose conclusion matches the goal           |
| `exact`     | Provide exactly the term needed                         |
| `have`      | Introduce intermediate results                          |
| `cases`     | Split on constructors of inductive types                |
| `induction` | Prove by induction on recursive types                   |
| `omega`     | Solve linear arithmetic                                 |
| `decide`    | Compute decidable propositions                          |
| `rw`        | Rewrite using an equality                               |

These twelve tactics will carry you through most of what follows.

## Exercises

The best way to learn tactics is to use them. These exercises progress from straightforward applications of single tactics to combinations that require reading the goal state carefully.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:exercises}}
```

If you get stuck, ask yourself: what is the shape of my goal? What tactic handles that shape? What hypotheses do I have available? The Infoview is your guide.

## The Liar's Trap

Try to prove something false:

```lean
{{#include ../../src/ZeroToQED/Proving.lean:liars_trap}}
```

Every tactic fails. `rfl` cannot make 0 equal 1. `simp` finds nothing to simplify. `omega` knows arithmetic and refuses. `decide` computes the answer and it is `false`. The goal state sits there, immovable: `⊢ 0 = 1`. You can stare at it, curse at it, try increasingly desperate combinations. Nothing works because nothing can work. The machine will not let you prove a falsehood.

This is the point. The compiler is not your collaborator; it is your adversary. It checks every step and rejects handwaving. When someone tells you their code is correct, you can ask: does it typecheck? When someone tells you their proof is valid, you can ask: did the machine accept it? The answers are not always the same, but when they are, you know something real.

## De Morgan's Little Theorem

[Augustus De Morgan](https://en.wikipedia.org/wiki/Augustus_De_Morgan) formalized the laws that bear his name in the 1850s: the negation of a conjunction is the disjunction of negations, and vice versa. Every programmer knows these laws intuitively from boolean expressions. Let us prove one.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:demorgan_project}}
```

The proof proceeds by case analysis. We have `h : ¬(P ∧ Q)`, a proof that `P ∧ Q` is false. We must show `¬P ∨ ¬Q`. The `by_cases` tactic splits on whether `P` holds:

- If `P` is true (call this `hp`), we go right and prove `¬Q`. Why? If `Q` were true, then `P ∧ Q` would be true, contradicting `h`. So `¬Q`.
- If `P` is false (call this `hnp`), we go left and prove `¬P` directly. We have it: `hnp`.

Each branch uses tactics from this article: `intro`, `apply`, `exact`, `left`, `right`, `constructor`. The `contradiction` tactic spots when hypotheses conflict. Read the proof slowly, watch the goal state at each step, and trace how the logical structure maps to the tactic sequence. This is the texture of real mathematics: case splits, contradictions, and the steady narrowing of possibilities until only truth remains.

De Morgan died in 1871. His laws persist in every boolean expression, every logic gate, every conditional branch. If you want to test your understanding, try proving the other direction: from `¬P ∨ ¬Q` to `¬(P ∧ Q)`. It is easier, which tells you something about the asymmetry of classical logic.

## The Theory Beneath

You can now prove things. The proofs have been simple, but the mental model is in place. You understand goals, hypotheses, and the tactic dance that connects them. Next we introduce type theory and dependent types, the language for stating claims worth proving.
