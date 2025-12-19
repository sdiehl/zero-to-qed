/-
Proof Strategy Examples

Examples demonstrating common proof patterns and strategies.
-/

import Mathlib.Tactic

namespace ZeroToQED.ProofStrategy

-- ANCHOR: goal_state_example
-- A typical induction proof showing goal state evolution
theorem double_sum (n : Nat) : 2 * n = n + n := by
  induction n with
  | zero =>
    -- Goal state: ⊢ 2 * 0 = 0 + 0
    rfl
  | succ n ih =>
    -- Goal state here:
    -- n : Nat
    -- ih : 2 * n = n + n
    -- ⊢ 2 * (n + 1) = (n + 1) + (n + 1)
    omega
-- ANCHOR_END: goal_state_example

-- ANCHOR: introduction_tactics
-- Introduction tactics: moving from goal to context

-- intro moves implications into the context
theorem intro_example (P Q : Prop) : P → Q → P := by
  intro hp  -- assumes P, calling it hp
  intro _   -- assumes Q (unused)
  exact hp  -- goal is now P, which we have

-- intro works with forall too
theorem forall_intro (P : Nat → Prop) (h : ∀ n, P n) : ∀ m, P m := by
  intro m   -- introduces arbitrary m
  exact h m -- apply universal hypothesis
-- ANCHOR_END: introduction_tactics

-- ANCHOR: elimination_tactics
-- Elimination tactics: using hypotheses to transform goals

-- cases eliminates disjunctions
theorem cases_example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl p => exact hp p  -- left case: we have P
  | inr q => exact hq q  -- right case: we have Q

-- And.left/right eliminate conjunctions
theorem and_elim (P Q : Prop) (h : P ∧ Q) : P := h.1

-- exists elimination via obtain
theorem exists_elim (P : Nat → Prop) (h : ∃ n, P n ∧ n > 0) : ∃ m, P m := by
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, hn⟩
-- ANCHOR_END: elimination_tactics

-- ANCHOR: rewriting_tactics
-- Rewriting tactics: transforming goals with equalities

theorem rewrite_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]      -- goal becomes b = c
  rw [h2]      -- goal becomes c = c
  -- or: rw [h1, h2] in one step

theorem rewrite_reverse (a b : Nat) (h : a = b) : b = a := by
  rw [← h]     -- rewrite right-to-left using ←

theorem simp_example (xs : List Nat) : (xs ++ []).length = xs.length := by
  simp         -- applies simp lemmas automatically
-- ANCHOR_END: rewriting_tactics

-- ANCHOR: direct_proof
-- Direct proof: apply implication and provide hypothesis
theorem direct (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp
-- ANCHOR_END: direct_proof

-- ANCHOR: proof_by_cases
-- Case analysis: split into cases and handle each
theorem by_cases_template (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero => left; rfl
  | succ m => right; simp
-- ANCHOR_END: proof_by_cases

-- ANCHOR: proof_by_induction
-- Induction: prove base case, then prove successor using IH
theorem by_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]
-- ANCHOR_END: proof_by_induction

-- ANCHOR: proof_by_contradiction
-- Contradiction: assume negation, derive False
theorem by_contradiction (P : Prop) (h : ¬¬P) : P := by
  by_contra hnp
  exact h hnp
-- ANCHOR_END: proof_by_contradiction

-- ANCHOR: proof_by_contraposition
-- Contraposition: prove ¬Q → ¬P instead of P → Q
theorem by_contraposition (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  intro hp
  by_contra hnq
  exact h hnq hp
-- ANCHOR_END: proof_by_contraposition

-- ANCHOR: backward_reasoning
-- Backward reasoning: working from goal toward hypotheses

-- apply works backward from the goal
theorem backward_example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  apply hqr   -- goal becomes Q (we need to prove what hqr needs)
  apply hpq   -- goal becomes P
  exact hp    -- we have P

-- have introduces intermediate lemmas
theorem have_example (a b : Nat) (ha : a > 5) (hb : b < 10) : a + b > 5 := by
  have h1 : a ≥ 6 := ha
  have h2 : b ≥ 0 := Nat.zero_le b
  omega
-- ANCHOR_END: backward_reasoning

-- ANCHOR: forward_reasoning
-- Forward reasoning: building from hypotheses toward goal

-- calc chains equational reasoning
theorem calc_example (a b c : Nat) (h1 : a = b + 1) (h2 : b = c + 1) : a = c + 2 := by
  calc a = b + 1 := h1
       _ = (c + 1) + 1 := by rw [h2]
       _ = c + 2 := by ring

-- obtain destructs existentials and conjunctions
theorem obtain_example (h : ∃ n : Nat, n > 0 ∧ n < 10) : ∃ m, m < 10 := by
  obtain ⟨n, _, hlt⟩ := h
  exact ⟨n, hlt⟩
-- ANCHOR_END: forward_reasoning

-- ANCHOR: induction_patterns
-- Induction patterns

-- Simple structural induction on Nat
theorem nat_induction (P : Nat → Prop) (base : P 0) (step : ∀ n, P n → P (n + 1))
    : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih

-- Strong induction when you need smaller cases
theorem strong_induction (n : Nat) (h : n > 0) : n ≥ 1 := by
  omega  -- trivial here, but pattern matters

-- Induction on lists
theorem list_induction (xs : List Nat) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]
-- ANCHOR_END: induction_patterns

-- ANCHOR: case_splitting
-- Case splitting strategies

-- split_ifs handles if-then-else
def abs (n : Int) : Int := if n < 0 then -n else n

theorem abs_nonneg (n : Int) : abs n ≥ 0 := by
  unfold abs
  split_ifs with h
  · omega  -- case: n < 0, so -n ≥ 0
  · omega  -- case: n ≥ 0

-- by_cases for arbitrary propositions
theorem by_cases_example (P : Prop) [Decidable P] : P ∨ ¬P := by
  by_cases h : P
  · left; exact h
  · right; exact h

-- interval_cases for bounded natural numbers
theorem small_cases (n : Nat) (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by
  omega
-- ANCHOR_END: case_splitting

-- ANCHOR: contradiction
-- Proof by contradiction

theorem contradiction_example (P : Prop) (h : P) (hn : ¬P) : False := by
  exact hn h  -- ¬P is P → False

theorem by_contra_example (n : Nat) (h : ¬(n = 0)) : n > 0 := by
  by_contra h'
  push_neg at h'
  omega
-- ANCHOR_END: contradiction

-- ANCHOR: automation_choice
-- Choosing the right automation

-- omega for linear arithmetic
theorem omega_example (a b : Nat) (h : a + b = 10) (h2 : a ≤ 3) : b ≥ 7 := by
  omega

-- ring for polynomial identities
theorem ring_example (x y : Int) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

-- simp for definitional simplification
theorem simp_list (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  simp

-- aesop for general proof search
theorem aesop_example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  aesop
-- ANCHOR_END: automation_choice

end ZeroToQED.ProofStrategy
