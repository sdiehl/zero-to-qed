import Mathlib.Tactic

/-!
# Proofs

Basics of proving in Lean, bridging the gap between programming and theorem proving.
-/

namespace ZeroToQED.Proving

-- ANCHOR: first_proof
-- Your very first proof: 1 + 1 = 2
theorem one_plus_one : 1 + 1 = 2 := by
  rfl

-- Without tactics, just a direct proof term
theorem one_plus_one' : 1 + 1 = 2 := rfl
-- ANCHOR_END: first_proof

-- ANCHOR: equality_basics
-- Equality is reflexive: everything equals itself
theorem eq_self (n : Nat) : n = n := by
  rfl

-- Equality is symmetric: if a = b then b = a
theorem eq_symm (a b : Nat) (h : a = b) : b = a := by
  rw [h]

-- Equality is transitive: if a = b and b = c then a = c
theorem eq_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]
-- ANCHOR_END: equality_basics

-- ANCHOR: goal_state_demo
-- Demonstrating how the goal state changes
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  simp
-- ANCHOR_END: goal_state_demo

-- ANCHOR: rfl_examples
-- rfl works when both sides compute to the same value
theorem two_times_three : 2 * 3 = 6 := by rfl

theorem list_length : [1, 2, 3].length = 3 := by rfl

theorem string_append : "hello " ++ "world" = "hello world" := by rfl

theorem bool_and : true && false = false := by rfl

def double (n : Nat) : Nat := n + n

theorem double_two : double 2 = 4 := by rfl
-- ANCHOR_END: rfl_examples

-- ANCHOR: trivial_examples
theorem true_is_true : True := by
  trivial

theorem one_le_two : 1 ≤ 2 := by
  trivial

theorem and_true : True ∧ True := by
  trivial
-- ANCHOR_END: trivial_examples

-- ANCHOR: simp_examples
theorem add_zero_simp (n : Nat) : n + 0 = n := by
  simp

theorem zero_add_simp (n : Nat) : 0 + n = n := by
  simp

theorem silly_arithmetic : (1 + 0) * (2 + 0) + 0 = 2 := by
  simp

theorem list_append_nil {α : Type*} (xs : List α) : xs ++ [] = xs := by
  simp

theorem use_hypothesis (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  simp [h]
-- ANCHOR_END: simp_examples

-- ANCHOR: intro_apply
-- intro: move assumptions from goal into context
theorem imp_self (P : Prop) : P → P := by
  intro hp
  exact hp

-- apply: use a lemma whose conclusion matches the goal
theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

-- intro with universal quantifiers
theorem forall_self (P : Nat → Prop) : (∀ n, P n) → (∀ n, P n) := by
  intro h n
  exact h n
-- ANCHOR_END: intro_apply

-- ANCHOR: have_example
-- have: introduce intermediate results
theorem have_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  have step : a = b := h1
  rw [step, h2]

theorem sum_example (n : Nat) : n + n = 2 * n := by
  have h : 2 * n = n + n := by ring
  rw [h]
-- ANCHOR_END: have_example

-- ANCHOR: cases_example
theorem bool_cases (b : Bool) : b = true ∨ b = false := by
  cases b with
  | true => left; rfl
  | false => right; rfl

theorem nat_zero_or_succ (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero => left; rfl
  | succ m => right; simp

theorem option_destruct (o : Option Nat) : o = none ∨ ∃ n, o = some n := by
  cases o with
  | none => left; rfl
  | some n => right; exact ⟨n, rfl⟩
-- ANCHOR_END: cases_example

-- ANCHOR: induction_example
theorem sum_twice (n : Nat) : n + n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => omega

theorem length_append {α : Type*} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; ring
-- ANCHOR_END: induction_example

-- ANCHOR: omega_example
theorem omega_simple (n : Nat) (h : n < 10) : n < 100 := by
  omega

theorem omega_transitive (a b c : Int) (h1 : a < b) (h2 : b < c) : a < c := by
  omega

theorem omega_sum (x y : Nat) (h : x + y = 10) : x ≤ 10 := by
  omega
-- ANCHOR_END: omega_example

-- ANCHOR: decide_example
theorem three_lt_five : (3 : Nat) < 5 := by
  decide

theorem bool_compute : (true && false) = false := by
  decide

theorem list_membership : 3 ∈ [1, 2, 3, 4, 5] := by
  decide

theorem fin_in_bounds : (2 : Fin 5).val < 5 := by
  decide
-- ANCHOR_END: decide_example

-- ANCHOR: proof_workflow
theorem worked_example (n : Nat) : n + 0 = 0 + n := by
  simp

theorem worked_example2 (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
-- ANCHOR_END: proof_workflow

-- ANCHOR: combining_tactics
theorem combined_proof (n : Nat) (h : n > 0) : n - 1 + 1 = n := by
  omega

theorem list_nonempty (xs : List Nat) (h : xs ≠ []) : xs.length > 0 := by
  cases xs with
  | nil => contradiction
  | cons x xs' => simp
-- ANCHOR_END: combining_tactics

/-!
## Exercises

Practice problems for the tactics introduced in this chapter.
-/

-- ANCHOR: exercises
-- Exercise 1: Use rfl to prove this computation
theorem ex_rfl : 3 * 4 = 12 := by
  rfl

-- Exercise 2: Use simp to simplify this expression
theorem ex_simp (n : Nat) : n * 1 + 0 = n := by
  simp

-- Exercise 3: Use intro and exact
theorem ex_intro_exact (P Q : Prop) (h : P) (hpq : P → Q) : Q := by
  exact hpq h

-- Exercise 4: Use cases to prove this about booleans
theorem ex_bool_not_not (b : Bool) : !!b = b := by
  cases b <;> rfl

-- Exercise 5: Use induction to prove addition is commutative
theorem ex_add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ n ih => omega

-- Exercise 6: Use omega to prove this inequality
theorem ex_omega (x y : Nat) (h1 : x ≤ 5) (h2 : y ≤ 3) : x + y ≤ 8 := by
  omega

-- Exercise 7: Combine multiple tactics
theorem ex_combined (xs : List Nat) : ([] ++ xs).length = xs.length := by
  simp

-- Exercise 8: Prove implication transitivity
theorem ex_imp_chain (A B C D : Prop) : (A → B) → (B → C) → (C → D) → A → D := by
  intro hab hbc hcd ha
  exact hcd (hbc (hab ha))

-- Exercise 9: Use cases on a natural number
theorem ex_nat_lt (n : Nat) : n = 0 ∨ 0 < n := by
  cases n with
  | zero => left; rfl
  | succ m => right; omega

-- Exercise 10: Prove a property about list reversal
theorem ex_reverse_nil : ([] : List Nat).reverse = [] := by
  rfl
-- ANCHOR_END: exercises

-- ANCHOR: liars_trap
-- Try to prove something false. Every tactic will fail.
theorem liar : 0 = 1 := by
  sorry  -- Try: rfl, simp, omega, decide. Nothing works.

-- The goal state shows: ⊢ 0 = 1
-- This goal is unprovable because it is false.
-- ANCHOR_END: liars_trap

-- ANCHOR: demorgan_project
-- De Morgan's Law: ¬(P ∧ Q) → (¬P ∨ ¬Q)
theorem demorgan (P Q : Prop) (h : ¬(P ∧ Q)) : ¬P ∨ ¬Q := by
  by_cases hp : P
  · -- Case: P is true
    right
    intro hq
    apply h
    constructor
    · exact hp
    · exact hq
  · -- Case: P is false
    left
    exact hp
-- ANCHOR_END: demorgan_project

-- ANCHOR: godel_gentzen
-- Gödel (1933) and Gentzen (1936) independently discovered that classical
-- logic embeds into intuitionistic logic via double-negation translation.
-- A classical proof of P becomes a constructive proof of ¬¬P.
-- Truth is preserved; only the computational witness is lost.
def DoubleNegation (P : Prop) : Prop := ¬¬P

-- Classical axioms become provable under double negation
theorem lem_double_neg (P : Prop) : DoubleNegation (P ∨ ¬P) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

-- Double negation is a monad: pure and bind
theorem dn_pure {P : Prop} (h : P) : DoubleNegation P :=
  fun hnp => hnp h

theorem dn_bind {P Q : Prop} (h : DoubleNegation P) (f : P → DoubleNegation Q) :
    DoubleNegation Q :=
  fun hnq => h (fun hp => f hp hnq)
-- ANCHOR_END: godel_gentzen

end ZeroToQED.Proving
