# Proofs

You have written functions. You have defined types. You have pattern matched, recursed, and composed. But you have not yet proved anything.

The difference matters. When you write a function, the compiler checks that types align, but it does not verify that your code does what you claim. You say this function sorts? The compiler shrugs. In theorem proving, you make claims and then justify them. The compiler verifies that your justification actually establishes the claim. You cannot bluff your way through a proof.

A bear learns to fish by watching the stream, understanding where salmon pause, developing patience for the moment when motion becomes certainty. Proving is similar. You learn to read the goal state, understand where progress stalls, develop patience for the tactic that transforms confusion into clarity.

## Programming and Proving

Lean unifies programming and theorem proving through type theory. The same language that lets you define a function also lets you state and prove properties about it. Understanding how these fit together is essential before writing your first proof.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:programming_and_proving}}
```

The `factorial` function computes values. It has **computational content** because it produces output from input. At runtime, it runs and returns numbers.

The `factorial_pos` theorem proves that factorial always returns a positive number. This proof convinces the type checker that the property holds, but it does not compute anything useful at runtime. The proof exists only to satisfy Lean's verification. Once the compiler confirms the proof is valid, the proof term itself can be discarded. Proofs are checked at compile time and deleted before the program runs.

The proof uses `omega`, a decision procedure for linear arithmetic that we cover later in this chapter. For now, just note that it automatically handles numeric inequalities.

The distinction between `def` and `theorem` reflects this. Both define named values, but `theorem` marks its body as **opaque**: Lean will never unfold it during type checking. This prevents proofs from slowing down type checking when they appear in types (since proofs are erased before runtime, they cannot affect execution speed). A `def` can be unfolded and computed with; a `theorem` cannot. If you need a lemma that Lean should simplify through, use `def` or mark the theorem with `@[simp]`.

What about proofs that appear as function arguments?

```lean
{{#include ../../src/ZeroToQED/Proving.lean:safe_div}}
```

The proof `h` ensures at compile time that you cannot call `safeDiv` with a zero divisor. But at runtime, `h` vanishes. The compiled code receives only `n` and `d`. This is the power of Lean's type system: proofs enforce invariants during development, then disappear from the final executable.

## Notation

Before we write our first proof, we need a shared language. The notation below bridges three worlds: the mathematical symbols you find in logic textbooks, the inference rules used in programming language theory (as in Pierce's [Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) and Harper's [Practical Foundations for Programming Languages](http://www.cs.cmu.edu/~rwh/pfpl/)), and the Lean syntax you will write. Learning to read all three simultaneously is the key to fluency.

| Symbol    | Name      | Meaning                             |
| --------- | --------- | ----------------------------------- |
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

Each logical connective and type former comes with two kinds of rules. **Introduction rules** tell you how to construct a proof or value: to prove `P ∧ Q`, prove both `P` and `Q`. **Elimination rules** tell you how to use a proof or value: from `P ∧ Q`, you can extract `P` or `Q`. This pattern is universal. For implication, introduction is `fun h => ...` (assume the premise), elimination is function application (use the implication). For existence, introduction provides a witness, elimination uses the witness. Once you internalize this pattern, you can work with any connective by asking: "How do I build one?" and "How do I use one?"

## Tactics as Proof-State Transformers

You may have repressed the trauma of high school algebra, but the core idea was sound: you start with $2x + 5 = 11$ and apply operations until you reach $x = 3$. Subtract 5, divide by 2, each step transforming the equation into something simpler. The tedium was doing it by hand, error-prone and joyless. But the method itself, symbolic manipulation through mechanical transformation, turns out to be extraordinarily powerful when the machine handles the bookkeeping.

Tactics work the same way. You start with a **goal** (what you want to prove) and a context (what you already know). Each **tactic** transforms the goal into simpler **subgoals**. You keep applying tactics until no goals remain. The proof is the sequence of transformations, not a single flash of insight.

Think of it as a game. Your current position is the proof state: the facts you hold and the destination you seek. Each tactic is a legal move that changes your position. Some moves split one goal into two (like `constructor` creating two subgoals). Some moves close a goal entirely (like `rfl` finishing with a checkmate). You win when the board is empty.

Formally, a **proof state** is a judgment $\Gamma \vdash G$: context $\Gamma$, goal $G$. A tactic transforms one proof state into zero or more new proof states. When no goals remain, the proof is complete. This table is your Rosetta Stone:

| Tactic          | Before                            | After                                                   | Rule                             |
| --------------- | --------------------------------- | ------------------------------------------------------- | -------------------------------- |
| `intro h`       | $\Gamma \vdash P \to Q$           | $\Gamma, h:P \vdash Q$                                  | $\to$-intro                      |
| `apply f`       | $\Gamma \vdash Q$                 | $\Gamma \vdash P$                                       | $\to$-elim (given $f : P \to Q$) |
| `exact h`       | $\Gamma, h:P \vdash P$            | $\square$                                               | assumption                       |
| `rfl`           | $\Gamma \vdash t = t$             | $\square$                                               | refl                             |
| `constructor`   | $\Gamma \vdash P \land Q$         | $\Gamma \vdash P$, $\Gamma \vdash Q$                    | $\land$-intro                    |
| `left`          | $\Gamma \vdash P \lor Q$          | $\Gamma \vdash P$                                       | $\lor$-intro₁                    |
| `right`         | $\Gamma \vdash P \lor Q$          | $\Gamma \vdash Q$                                       | $\lor$-intro₂                    |
| `cases h`       | $\Gamma, h:P \lor Q \vdash R$     | $\Gamma, h:P \vdash R$, $\Gamma, h:Q \vdash R$          | $\lor$-elim                      |
| `induction n`   | $\Gamma \vdash \forall n,\, P(n)$ | $\Gamma \vdash P(0)$, $\Gamma, ih:P(k) \vdash P(k{+}1)$ | Nat-ind                          |
| `rw [h]`        | $\Gamma, h: a=b \vdash P[a]$      | $\Gamma, h:a=b \vdash P[b]$                             | subst                            |
| `simp`          | $\Gamma \vdash G$                 | $\Gamma \vdash G'$                                      | rewrite*                         |
| `contradiction` | $\Gamma, h:\bot \vdash P$         | $\square$                                               | $\bot$-elim                      |

The symbol $\square$ marks a completed goal. Multiple goals after "After" mean the tactic created subgoals. Read left to right: you have the state on the left, you apply the tactic, you must now prove everything on the right. This is the algebra of proof. Each tactic is a function from proof states to proof states, and a complete proof is a composition that maps your theorem to $\square$.

**Reading the notation**: In expressions like $\Gamma, h:a=b \vdash P[a]$, the comma separates hypotheses (the "extended context"), the colon separates a hypothesis name from its type, and the turnstile $\vdash$ separates what you have from what you must prove. Lean's InfoView displays this vertically, one hypothesis per line:

```
h : a = b
⊢ P[a]
```

The horizontal notation packs the same information into table cells. Once you can read one, you can read the other.

If the table above looks like both logic and programming, that is not a coincidence.

## Proving vs Programming

The surprising insight is that proving and programming are the same activity viewed differently. A proof is a program. A theorem is a type. When you prove $P \to Q$, you are writing a function that transforms evidence for $P$ into evidence for $Q$. This correspondence, the **Curry-Howard isomorphism**, means that logic and computation are two views of the same underlying structure:

| Logic           | Programming              |
| --------------- | ------------------------ |
| **proposition** | type                     |
| **proof**       | program                  |
| $P \to Q$       | function from `P` to `Q` |
| $P \land Q$     | pair `(P, Q)`            |
| $P \lor Q$      | either `P` or `Q`        |
| $\top$          | unit type                |
| $\bot$          | empty type               |

Every function you have written so far was secretly a proof. Every proof you write from now on is secretly a program. Two cultures, mathematicians and programmers, spoke the same language for decades without knowing it.

## What You Already Know

The concepts from Arc I are not prerequisites for Arc II. They are the same concepts in different clothing. If you understood programming in Lean, you already understand proving. The vocabulary changes; the structures do not.

| Arc I (Programming)                        | Arc II (Proving)                               | Why They Match                                                    |
| ------------------------------------------ | ---------------------------------------------- | ----------------------------------------------------------------- |
| Pattern matching on `Nat` constructors     | The `cases` tactic on natural numbers          | Both examine which constructor built the value                    |
| Recursive function with base case          | Proof by `induction` with base case            | Both reduce a problem on \\(n+1\\) to the same problem on \\(n\\) |
| Function type signature `α → β`            | Theorem statement `P → Q`                      | Both declare what goes in and what comes out                      |
| Function body (the implementation)         | Proof term (the justification)                 | Both witness that the signature/statement is inhabited            |
| Returning a value of type `α`              | Providing a term of type `P` (a proof of `P`)  | Both construct an inhabitant of the required type                 |
| `match x with \| none => ... \| some a =>` | `cases h with \| none => ... \| some a => ...` | Both split on constructors and handle each possibility            |
| Termination checking on recursive calls    | Well-founded induction on decreasing measures  | Both ensure the process ends                                      |
| Type error: expected `β`, got `γ`          | Proof error: expected `Q`, got `R`             | Both mean you produced the wrong thing                            |

When you wrote `match n with | 0 => ... | n + 1 => ...` in the [Control Flow](./07_control_flow.md) article, you were doing case analysis. The `cases n` tactic does the same thing to a proof goal. When you wrote a recursive function that called itself on `n` to compute a result for `n + 1`, you were doing induction. The `induction n` tactic generates exactly that structure: a base case and a step that assumes the result for `n`.

The syntax differs because tactics operate on proof states rather than values directly. But the reasoning is identical. If you can write a recursive function over natural numbers, you can prove a theorem about natural numbers. You have been training for this.

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

**How does definitional equality relate to other equality types?** Definitional equality is the strongest: if `a` and `b` are definitionally equal, `rfl` proves `a = b` with no computation. Decidable equality (via `DecidableEq` and `decide`, discussed in [Polymorphism](./08_polymorphism.md)) handles cases where equality can be computed at runtime, like `5 = 5` or `"hello" = "hello"`. Propositional equality (`a = b` as a `Prop`) is the most general: you may need lemmas and rewriting to prove it. All three describe the same `=` type, but they differ in how much work is required to establish the proof.

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

## Using Hypotheses: `exact`

The simplest way to close a goal is to provide exactly what is needed. If your goal is `P` and you have a hypothesis `h : P`, then `exact h` finishes the proof.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:exact_example}}
```

The `exact` tactic says "this term has exactly the type we need." It works with any expression, not just hypothesis names. If `f : P → Q` and `h : P`, then `exact f h` proves `Q`.

## Introducing Assumptions: `intro`

When your goal is an **implication** $P \to Q$, you assume $P$ and prove $Q$. This is the introduction rule for implication:

\\[
\frac{\Gamma, P \vdash Q}{\Gamma \vdash P \to Q} \text{(→-intro)}
\\]

Read this bottom-up: to prove $P \to Q$ (below the line), it suffices to prove $Q$ while assuming $P$ (above the line). The `intro` tactic performs this transformation, moving the antecedent from goal to hypothesis.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:intro_simple}}
```

After `intro hp`, the goal changes from `P → P` to just `P`, and you gain hypothesis `hp : P`. Multiple assumptions can be introduced at once: `intro h1 h2 h3`.

The same tactic handles universal quantifiers. When your goal is `∀ n, P n`, `intro n` introduces `n` as a variable in scope:

```lean
{{#include ../../src/ZeroToQED/Proving.lean:intro_forall}}
```

## Applying Lemmas: `apply`

The `apply` tactic performs **backward reasoning**. When your goal is $Q$ and you have $h : P \to Q$, applying $h$ transforms the goal to $P$. You reason backward from what you want to what you need. This is the elimination rule for implication:

\\[
\frac{\Gamma \vdash P}{\Gamma, h : P \to Q \vdash Q} \text{(→-elim with apply)}
\\]

Read this as: if you can prove $P$, and you have $h : P \to Q$, then you can prove $Q$. The `apply` tactic inverts this: to prove $Q$, it suffices to prove $P$.

```lean
{{#include ../../src/ZeroToQED/Proving.lean:apply_example}}
```

In `imp_trans`, we have three implications chained together: $(P \to Q) \to (Q \to R) \to P \to R$. This reads as "if P implies Q, and Q implies R, then P implies R." The arrows associate to the right, so it parses as $(P \to Q) \to ((Q \to R) \to (P \to R))$. After introducing all hypotheses, the goal is `R`. We apply `hqr : Q → R` to reduce the goal to `Q`, then apply `hpq : P → Q` to reduce it to `P`, then `exact hp` closes it.

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

The syntax `⟨n, rfl⟩` in the last example is **anonymous constructor notation**. The goal `∃ n, o = some n` requires a witness and a proof. The angle brackets `⟨...⟩` construct the existential: `n` is the witness, and `rfl` proves `o = some n` (since in this branch, `o` is definitionally `some n`). This is equivalent to writing `Exists.intro n rfl`.

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

## Axioms and Escape Hatches

The **`axiom`** declaration asserts something without proof. It is the escape hatch from the proof system: you declare that something is true and Lean believes you. This is extremely dangerous. If you assert something false, you can prove anything at all, including `False` itself. The system becomes unsound.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:axiom_example}}
```

> [!WARNING]
> **Axioms** should be used only in narrow circumstances: foundational assumptions like the law of excluded middle or the axiom of choice (which Mathlib already provides), FFI bindings where proofs are impossible because the implementation is external, or as temporary placeholders during development (though `sorry` is preferred since it generates a warning). Before adding a custom axiom, ask whether you actually need it. Usually the answer is no.

Lean's **kernel** accepts axioms unconditionally. The `#print axioms` command shows which axioms a theorem depends on, which is useful for verifying that your proofs rely only on the standard foundational axioms you expect.

The **`opaque`** declaration hides a definition's implementation from the type checker. Unlike `axiom`, an opaque definition must be provided, but Lean treats it as a black box during type checking. This is useful when you want to abstract implementation details while still having a concrete definition.

```lean
{{#include ../../src/ZeroToQED/Basics.lean:opaque_example}}
```

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
