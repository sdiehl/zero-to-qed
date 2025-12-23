# Tactics Reference

[Robin Milner](https://en.wikipedia.org/wiki/Robin_Milner)'s [LCF system](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions) introduced a radical idea in the 1970s: let users extend the theorem prover with custom proof procedures, but channel all proof construction through a small trusted kernel. You could write arbitrarily clever automation, and if it produced a proof, that proof was guaranteed valid. Tactics are this idea fully realized. They are programs that build proofs, metaprograms that manipulate the proof state, search procedures that explore the space of possible arguments. When you write `simp` and Lean simplifies your goal through dozens of rewrite steps, you are invoking a sophisticated algorithm. When you write `omega` and Lean discharges a linear arithmetic obligation, you are running a decision procedure. The proof terms these tactics construct may be enormous, but they are checked by the kernel, and the kernel is small enough to trust. Think of tactics as the code you write, and the kernel as the one colleague who actually reads your pull requests.

## Table of Contents

The following covers all the major tactics in Lean 4 and Mathlib. Click on any tactic name to jump to its documentation and examples.

- [`abel`](#abel) - Prove equalities in abelian groups
- [`aesop`](#aesop) - General automation tactic
- [`all_goals`](#all_goals) - Apply tactic to all current goals
- [`any_goals`](#any_goals) - Apply tactic to any applicable goal
- [`apply`](#apply) - Apply hypotheses or lemmas to solve goals
- [`apply_fun`](#apply_fun) - Apply function to both sides of equality
- [`assumption`](#assumption) - Use hypothesis matching goal
- [`bound`](#bound) - Prove inequalities from structure
- [`by_cases`](#by_cases) - Perform case splitting
- [`by_contra`](#by_contra) - Proof by contradiction
- [`calc`](#calc) - Chain equations and inequalities
- [`cases`](#cases) - Case analysis on inductive types
- [`choose`](#choose) - Extract choice function from forall-exists
- [`congr`](#congr) - Prove equality using congruence rules
- [`constructor`](#constructor) - Break down conjunctions, existentials, and iff
- [`contradiction`](#contradiction) - Find contradictions in hypotheses
- [`conv`](#conv) - Targeted rewriting in specific parts
- [`convert`](#convert) - Prove by showing goal equals type of expression
- [`decide`](#decide) - Run decision procedures
- [`exact`](#exact) - Provide an exact proof term
- [`exfalso`](#exfalso) - Prove anything from False
- [`ext`](#ext-extensionality) - Prove equality of functions extensionally
- [`field_simp`](#field_simp) - Simplify field expressions
- [`fin_cases`](#fin_cases) - Split finite type into cases
- [`first`](#first) - Try tactics until one succeeds
- [`focus`](#focus) - Limit tactics to first goal
- [`gcongr`](#gcongr) - Prove inequalities using congruence
- [`generalize`](#generalize) - Replace expressions with variables
- [`grind`](#grind) - Proof search using congruence closure
- [`group`](#group) - Prove equalities in groups
- [`have`](#have) - Introduce new hypotheses
- [`hint`](#hint) - Get tactic suggestions
- [`induction`](#induction) - Perform inductive proofs
- [`interval_cases`](#interval_cases) - Split bounded values into cases
- [`intro`](#intro) - Introduce assumptions from implications and quantifiers
- [`left`](#left-and-right) - Choose left side of disjunction
- [`lift`](#lift) - Lift variable to higher type
- [`linarith`](#linarith) - Prove linear inequalities
- [`linear_combination`](#linear_combination) - Prove from linear combinations
- [`module`](#module) - Prove equalities in modules
- [`nlinarith`](#nlinarith) - Handle nonlinear inequalities
- [`noncomm_ring`](#noncomm_ring) - Prove in non-commutative rings
- [`norm_cast`](#norm_cast) - Simplify by moving casts outward
- [`norm_num`](#norm_num) - Simplify numerical expressions
- [`nth_rw`](#nth_rw) - Rewrite only the nth occurrence
- [`obtain`](#obtain) - Destructure existentials and structures
- [`omega`](#omega) - Solve linear arithmetic over Nat and Int
- [`pick_goal`](#pick_goal) - Move specific goal to front
- [`positivity`](#positivity) - Prove positivity goals
- [`push_cast`](#push_cast) - Push casts inward
- [`push_neg`](#push_neg) - Push negations inward
- [`qify`](#qify) - Shift to rationals
- [`refine`](#refine) - Apply with holes to fill later
- [`rename`](#rename) - Rename hypotheses for clarity
- [`repeat`](#repeat) - Apply tactic repeatedly until fails
- [`revert`](#revert) - Move hypotheses back to the goal
- [`rfl`](#rfl-reflexivity) - Prove by reflexivity
- [`right`](#left-and-right) - Choose right side of disjunction
- [`ring`](#ring) - Prove equalities in commutative rings
- [`rw`](#rw-rewrite) - Rewrite using equalities
- [`simp`](#simp) - Apply simplification lemmas
- [`simp_all`](#simp_all) - Simplify everything including hypotheses
- [`simp_rw`](#simp_rw) - Rewrite with simplification at each step
- [`sorry`](#sorry) - Admit goal without proof
- [`specialize`](#specialize) - Instantiate hypothesis with specific arguments
- [`split`](#split) - Handle if-then-else and pattern matching
- [`split_ifs`](#split_ifs) - Case on if-then-else expressions
- [`subst`](#subst) - Substitute variable with its value
- [`swap`](#swap) - Swap first two goals
- [`symm`](#symm) - Swap symmetric relations
- [`tauto`](#tauto) - Prove logical tautologies
- [`trans`](#trans) - Split transitive relations
- [`trivial`](#trivial) - Prove simple goals automatically
- [`try`](#try) - Attempt tactic, continue if fails
- [`use`](#use) - Provide witnesses for existential goals
- [`zify`](#zify) - Shift natural numbers to integers

## Logical Connectives

### intro

The `intro` tactic moves hypotheses from the goal into the local context. When your goal is `∀ x, P x` or `P → Q`, using `intro` names the bound variable or assumption and makes it available for use in the proof.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:intro_apply}}
```

### constructor

The `constructor` tactic applies the first constructor of an inductive type to the goal. For `And` (conjunction), it splits the goal into two subgoals. For `Exists`, it expects you to provide a witness. For `Iff`, it creates subgoals for both directions.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:constructor}}
```

### left and right

The `left` and `right` tactics select which side of a disjunction to prove. When your goal is `P ∨ Q`, use `left` to commit to proving `P` or `right` to prove `Q`.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:left_right}}
```

### use

The `use` tactic provides a concrete witness for an existential goal. When your goal is `∃ x, P x`, using `use t` substitutes `t` for `x` and leaves you to prove `P t`.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:use_existential}}
```

### obtain

The `obtain` tactic extracts components from existential statements and structures in hypotheses. It combines `have` and pattern matching, letting you name both the witness and the proof simultaneously.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:have_obtain}}
```

## Applying Lemmas

### exact

The `exact` tactic closes a goal by providing a term whose type matches the goal exactly. It performs no additional unification or elaboration beyond what is necessary.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:exact_refine}}
```

### apply

The `apply` tactic works backwards from the goal. Given a lemma `h : A → B` and a goal `B`, using `apply h` reduces the goal to proving `A`. It unifies the conclusion of the lemma with the current goal.

### refine

The `refine` tactic is like `exact` but allows placeholders written as `?_` that become new goals. This lets you partially specify a proof term while deferring some parts.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:exact_refine}}
```

### convert

The `convert` tactic applies a term to the goal even when the types do not match exactly, generating side goals for the mismatches. It is useful when you have a lemma that is almost but not quite what you need.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:convert}}
```

### specialize

The `specialize` tactic instantiates a universally quantified hypothesis with concrete values, replacing the general statement with a specific instance in your context.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:specialize}}
```

## Context Manipulation

### have

The `have` tactic introduces a new hypothesis into the context. You state what you want to prove as an intermediate step, prove it, and then it becomes available for the rest of the proof.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:have_obtain}}
```

### rename

The `rename` tactic changes the name of a hypothesis in the local context, making proofs more readable when auto-generated names are unclear.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:rename}}
```

### revert

The `revert` tactic is the inverse of `intro`. It moves a hypothesis from the context back into the goal as an implication or universal quantifier, which is useful before applying induction or certain lemmas.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:revert}}
```

### generalize

The `generalize` tactic replaces a specific expression in the goal with a fresh variable, abstracting over that value. This is useful when you need to perform induction on a compound expression.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:generalize}}
```

## Rewriting and Simplifying

### rw (rewrite)

The `rw` tactic replaces occurrences of the left-hand side of an equality with the right-hand side. Use `rw [←h]` to rewrite in the reverse direction. Multiple rewrites can be chained in a single `rw [h1, h2, h3]`.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:rw_simp}}
```

> [!TIP]
> `rw` rewrites the first occurrence it finds. Use `rw [h] at hyp` to rewrite in a hypothesis instead of the goal. If rewriting fails due to dependent types or metavariables, try `simp_rw` which handles these cases more gracefully. Use `nth_rw n [h]` to target a specific occurrence.

### simp

The `simp` tactic repeatedly applies lemmas marked with `@[simp]` to simplify the goal. It handles common algebraic identities, list operations, and logical simplifications automatically.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:rw_simp}}
```

> [!TIP]
> Use `simp only [lemma1, lemma2]` for reproducible proofs. Bare `simp` can break when new simp lemmas are added to the library. Use `simp?` to see which lemmas were applied, then replace with `simp only [...]` for stability. In Mathlib code reviews, bare `simp` at non-terminal positions is discouraged.

### simp_all

The `simp_all` tactic simplifies both the goal and all hypotheses simultaneously, using each simplified hypothesis to help simplify the others.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:simp_all}}
```

### simp_rw

The `simp_rw` tactic rewrites using the given lemmas but applies simplification at each step, which helps when rewrites would otherwise fail due to associativity or other issues.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:simp_rw}}
```

### nth_rw

The `nth_rw` tactic rewrites only a specific occurrence of a pattern, counting from 1. This gives precise control when an expression appears multiple times and you only want to change one instance.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:nth_rewrite}}
```

### norm_num

The `norm_num` tactic evaluates and simplifies numeric expressions, proving goals like `2 + 2 = 4` or `7 < 10` by computation. It handles arithmetic in various number types.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:norm_num}}
```

### norm_cast

The `norm_cast` tactic normalizes expressions involving type coercions by pushing casts outward and combining them, making goals about mixed numeric types easier to prove.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:norm_cast}}
```

### push_cast

The `push_cast` tactic pushes type coercions inward through operations, distributing a cast over addition, multiplication, and other operations.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:push_cast}}
```

### conv

The `conv` tactic enters a conversion mode that lets you navigate to specific subexpressions and rewrite only there. It is invaluable when `rw` affects the wrong occurrence or when you need surgical precision.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:conv}}
```

> [!TIP]
> Navigation commands in `conv` mode: `lhs`/`rhs` select sides of an equation, `arg n` selects the nth argument, `ext` introduces binders, and `enter [1, 2]` navigates by path. Use `conv_lhs` or `conv_rhs` as shortcuts when you only need to work on one side of an equation.

## Reasoning with Relations

### rfl (reflexivity)

The `rfl` tactic proves goals of the form `a = a` where both sides are definitionally equal. It works even when the equality is not syntactically obvious but follows from definitions.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:rfl}}
```

### symm

The `symm` tactic reverses a symmetric relation like equality. If your goal is `a = b` and you have `h : b = a`, using `symm` on `h` or the goal makes them match.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:symm}}
```

### trans

The `trans` tactic splits a transitive goal like `a = c` into two subgoals `a = b` and `b = c` for a chosen intermediate value `b`. It works for any transitive relation.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:trans}}
```

### subst

The `subst` tactic eliminates a variable by substituting it everywhere with an equal expression. Given `h : x = e`, using `subst h` replaces all occurrences of `x` with `e` and removes `x` from the context.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:subst}}
```

### ext (extensionality)

The `ext` tactic proves equality of functions, sets, or structures by showing they agree on all inputs or components. It introduces the necessary variables and reduces the goal to pointwise equality.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:ext}}
```

### calc

The `calc` tactic provides a structured way to write chains of equalities or inequalities. Each step shows the current expression, the relation, and the justification, mirroring traditional mathematical proofs.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:calc_mode}}
```

### apply_fun

The `apply_fun` tactic applies a function to both sides of an equality hypothesis. It automatically generates a side goal requiring the function to be injective when needed.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:apply_fun}}
```

### congr

The `congr` tactic reduces an equality goal `f a = f b` to proving `a = b`, applying congruence recursively. It handles nested function applications by breaking them into component equalities.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:congr}}
```

### gcongr

The `gcongr` tactic proves inequalities by applying monotonicity lemmas. It automatically finds and applies lemmas showing that operations preserve ordering, such as adding to both sides of an inequality.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:gcongr}}
```

### linear_combination

The `linear_combination` tactic proves an equality by showing it follows from a linear combination of given hypotheses. You specify the coefficients, and it verifies the algebra.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:linear_combination}}
```

### positivity

The `positivity` tactic proves goals asserting that an expression is positive, nonnegative, or nonzero. It analyzes the structure of the expression and applies appropriate lemmas automatically.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:positivity}}
```

### bound

The `bound` tactic proves inequality goals by recursively analyzing expression structure and applying bounding lemmas. It is particularly effective for expressions built from well-behaved operations.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:bound}}
```

## Reasoning Techniques

### cases

The `cases` tactic performs case analysis on an inductive type, creating separate subgoals for each constructor. For a natural number, it splits into the zero case and the successor case.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:cases_induction}}
```

### induction

The `induction` tactic sets up a proof by induction on an inductive type. It creates a base case for each non-recursive constructor and an inductive case with an induction hypothesis for each recursive constructor.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:cases_induction}}
```

> [!TIP]
> Use `induction n with | zero => ... | succ n ih => ...` for structured case syntax. If your induction hypothesis is too weak, try `revert` on additional variables before inducting, or use `induction n generalizing x y` to strengthen the hypothesis. For mutual or nested induction, consider `induction ... using` with a custom recursor.

### split

The `split` tactic splits goals involving `if-then-else` expressions or pattern matching into separate cases. It creates subgoals for each branch with the appropriate condition as a hypothesis.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:split}}
```

### split_ifs

The `split_ifs` tactic finds all `if-then-else` expressions in the goal and splits on their conditions, creating cases for each combination of true and false branches.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:split_ifs}}
```

### contradiction

The `contradiction` tactic closes the goal by finding contradictory hypotheses in the context, such as `h1 : P` and `h2 : ¬P`, or an assumption of `False`.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:contradiction_exfalso}}
```

### exfalso

The `exfalso` tactic changes any goal to `False`, applying the principle of explosion. Use this when you can derive a contradiction from your hypotheses.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:contradiction_exfalso}}
```

### by_contra

The `by_contra` tactic starts a proof by contradiction. It adds the negation of the goal as a hypothesis and changes the goal to `False`, requiring you to derive a contradiction.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:by_contra}}
```

### push_neg

The `push_neg` tactic pushes negations through quantifiers and connectives using De Morgan's laws. It transforms `¬∀ x, P x` into `∃ x, ¬P x` and similar patterns.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:push_neg}}
```

### by_cases

The `by_cases` tactic splits the proof into two cases based on whether a proposition is true or false, adding the proposition as a hypothesis in one branch and its negation in the other.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:by_cases}}
```

### choose

The `choose` tactic extracts a choice function from a hypothesis of the form `∀ x, ∃ y, P x y`. It produces a function `f` and a proof that `∀ x, P x (f x)`.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:choose}}
```

### lift

The `lift` tactic replaces a variable with one of a more specific type when you have a proof justifying the lift. For example, lifting an integer to a natural number given a proof it is nonnegative.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:lift}}
```

### zify

The `zify` tactic converts a goal about natural numbers to one about integers, which often makes subtraction and other operations easier to handle since integers are closed under subtraction.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:zify}}
```

### qify

The `qify` tactic converts a goal about integers or naturals to one about rationals, enabling division and making certain algebraic manipulations possible.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:qify}}
```

## Searching

### assumption

The `assumption` tactic closes the goal if there is a hypothesis in the context that exactly matches. It searches through all available hypotheses to find one with the right type.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:assumption}}
```

### trivial

The `trivial` tactic tries a collection of simple tactics including `rfl`, `assumption`, and `contradiction` to close easy goals without you specifying which approach to use.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:trivial}}
```

### decide

The `decide` tactic evaluates decidable propositions by computation. For finite checks like `2 < 5` or membership in a finite list, it simply computes the answer and closes the goal.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:decide}}
```

> [!NOTE]
> `decide` works in the kernel and produces small proof terms but can be slow. `native_decide` compiles to native code and runs faster but produces larger proof terms that just assert the result. For quick checks use `decide`; for expensive computations like verifying grid states in our Game of Life proofs, `native_decide` is essential.

### hint

The `hint` tactic suggests which tactics might make progress on the current goal. It is a discovery tool that helps when you are unsure how to proceed.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:hint}}
```

## General Automation

### omega

The `omega` tactic is a decision procedure for linear arithmetic over natural numbers and integers. It handles goals involving addition, subtraction, multiplication by constants, and comparisons.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:omega}}
```

> [!NOTE]
> `omega` handles `Nat` and `Int` but not `Rat` or `Real`. It solves linear constraints but fails on nonlinear multiplication like `x * y < z`. For rationals, try `linarith` after `qify`. For nonlinear goals, try `nlinarith` or `polyrith`.

### linarith

The `linarith` tactic proves goals that follow from linear arithmetic over ordered rings. It combines hypotheses about inequalities to derive the goal using Fourier-Motzkin elimination.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:linarith}}
```

### nlinarith

The `nlinarith` tactic extends `linarith` to handle some nonlinear goals by first preprocessing with polynomial arithmetic before applying linear reasoning.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:nlinarith}}
```

### ring

The `ring` tactic proves polynomial equalities in commutative rings by normalizing both sides to a canonical form and checking if they match. It handles addition, multiplication, and powers.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:ring}}
```

### noncomm_ring

The `noncomm_ring` tactic proves equalities in non-commutative rings where multiplication order matters, such as matrix rings or quaternions.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:noncomm_ring}}
```

### field_simp

The `field_simp` tactic clears denominators in field expressions by multiplying through, reducing goals involving fractions to polynomial equalities that `ring` can handle.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:field_simp}}
```

### abel

The `abel` tactic proves equalities in abelian groups by normalizing expressions involving addition, subtraction, and negation to a canonical form.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:abel}}
```

### group

The `group` tactic proves equalities in groups using the group axioms. It handles multiplication, inverses, and the identity element, normalizing expressions to compare them.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:group}}
```

### module

The `module` tactic proves equalities in modules over a ring, handling scalar multiplication and vector addition to normalize expressions.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:module_tactic}}
```

### aesop

The `aesop` tactic is a general-purpose automation tactic that combines many strategies including simplification, introduction rules, and case splitting to solve goals automatically.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:aesop}}
```

> [!TIP]
> `aesop` is powerful but can be slow on complex goals. Use `aesop?` to see what it did, then extract a faster proof. Register custom lemmas with `@[aesop safe]` or `@[aesop unsafe 50%]` to extend its knowledge. The `safe` rules are always applied; `unsafe` rules are tried with backtracking weighted by percentage.

### grind

The `grind` tactic is one of Lean 4's most sophisticated automation tools. Under the hood, it maintains an [e-graph](https://en.wikipedia.org/wiki/E-graph) (equivalence graph), a data structure that efficiently represents equivalence classes of terms. When you assert `a = b`, the e-graph merges the equivalence classes containing `a` and `b`. The key insight is congruence: if `a = b`, then `f a = f b` for any function `f`. The e-graph propagates these consequences automatically.

The algorithm works in three phases. First, congruence closure processes all equalities and computes the transitive, symmetric, reflexive closure under function application. If you know $x = y$ and $f(x) = 10$, congruence closure deduces $f(y) = 10$ without explicit rewriting. Second, forward chaining applies implications: if you have $p \land q$ and $q \to r$, it extracts $q$ from the conjunction and fires the implication to derive $r$. Third, case splitting handles disjunctions and if-then-else expressions by exploring branches.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:grind}}
```

The power shows up when these mechanisms combine. Here `grind` chains four equalities through two functions to conclude `f b = 42`:

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:grind_complex}}
```

> [!TIP]
> `grind` excels at "obvious" goals that would require tedious manual rewriting. If your goal involves chained equalities, function congruence, or propositional reasoning, try `grind` before writing out the steps by hand. For debugging, `grind?` shows the proof term it constructs.

### tauto

The `tauto` tactic proves propositional tautologies involving $\land$, $\lor$, $\to$, $\leftrightarrow$, $\lnot$, `True`, and `False`. It handles classical and intuitionistic reasoning automatically.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:tauto}}
```

## Goal Operations

### sorry

The `sorry` tactic closes any goal without actually proving it, leaving a hole in the proof. Use it as a placeholder during development, but never in finished proofs as it makes theorems unsound.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:sorry_admit}}
```

> [!WARNING]
> Any theorem containing `sorry` is marked as unsound and propagates this flag to anything that depends on it. Use `#check @myTheorem` to see if a theorem is sorry-free. Mathlib rejects all PRs containing sorry. During development, `sorry` is invaluable for sketching proofs top-down, but treat each one as a debt to be paid.

### swap

The `swap` tactic exchanges the first two goals in the goal list, letting you work on the second goal first when that is more convenient.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:swap}}
```

### pick_goal

The `pick_goal` tactic moves a specific numbered goal to the front of the goal list, allowing you to address goals in any order you choose.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:pick_goal}}
```

### all_goals

The `all_goals` tactic applies a given tactic to every goal in the current goal list, which is useful when multiple goals can be solved the same way.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:all_goals}}
```

### any_goals

The `any_goals` tactic applies a given tactic to each goal where it succeeds, skipping goals where it fails. It succeeds if it makes progress on at least one goal.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:any_goals}}
```

### focus

The `focus` tactic restricts attention to the first goal, hiding all other goals. This helps ensure you complete one goal before moving to the next.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:focus}}
```

### try

The `try` tactic attempts to apply a tactic and succeeds regardless of whether the inner tactic succeeds or fails. It is useful for optional simplification steps.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:try}}
```

### first

The `first` tactic tries a list of tactics in order and uses the first one that succeeds. It fails only if all tactics fail.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:first}}
```

### repeat

The `repeat` tactic applies a given tactic repeatedly until it fails to make progress. It is useful for exhaustively applying a simplification or introduction rule.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:repeat}}
```

### Tactic Combinators

The semicolon `;` sequences tactics, while `<;>` applies the second tactic to all goals created by the first. These combinators help write concise proof scripts.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:tactic_combinators}}
```

## Domain-Specific Tactics

### interval_cases

The `interval_cases` tactic performs case analysis when a variable is known to lie in a finite range. Given bounds on a natural number, it generates a case for each possible value.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:interval_cases}}
```

### fin_cases

The `fin_cases` tactic performs case analysis on elements of a finite type like `Fin n` or `Bool`, creating a subgoal for each possible value of the type.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:fin_cases}}
```

## Working with Quantifiers

### Existential Quantifiers

Existential statements claim that some witness exists satisfying a property. To prove one, use `use` to provide the witness. To use an existential hypothesis, use `obtain` to extract the witness and its property.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:exists}}
```

### Universal Quantifiers

Universal statements claim a property holds for all values. To prove one, use `intro` to introduce an arbitrary value. To use a universal hypothesis, use `specialize` or simply apply it to a specific value.

```lean
{{#include ../../src/ZeroToQED/Tactics.lean:forall}}
```

## Using This Reference

You do not need to memorize this article. Bookmark it. When you encounter a goal you cannot close, return here and ask: what shape is my goal? Implication, conjunction, existential, equality? Find the matching section. The tactic you need is there. Over time, the common ones become muscle memory. The obscure ones remain here for when you need them.
