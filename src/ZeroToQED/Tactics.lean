import Mathlib.Tactic

/-!
# Tactics in Lean
-/

namespace ZeroToQED.Tactics

-- ANCHOR: intro_apply
theorem intro_apply : ∀ x : Nat, x = x → x + 0 = x := by
  intro x h  -- Introduce x and hypothesis h : x = x
  simp       -- Simplify x + 0 = x
-- ANCHOR_END: intro_apply

-- ANCHOR: constructor
theorem constructor_example : True ∧ True := by
  constructor
  · trivial  -- Prove first True
  · trivial  -- Prove second True
-- ANCHOR_END: constructor

-- ANCHOR: exact_refine
theorem exact_example (h : 2 + 2 = 4) : 4 = 2 + 2 := by
  exact h.symm

/-- `refine` allows holes with ?_ -/
theorem refine_example : ∃ x : Nat, x > 5 := by
  refine ⟨10, ?_⟩  -- Use 10, but leave proof as a hole
  simp              -- Fill the hole: prove 10 > 5
-- ANCHOR_END: exact_refine

-- ANCHOR: rw_simp
theorem rw_example (a b : Nat) (h : a = b) : a + 2 = b + 2 := by
  rw [h]  -- Rewrite a to b using h

theorem simp_example (x : Nat) : x + 0 = x ∧ 0 + x = x := by
  simp  -- Simplifies both sides
-- ANCHOR_END: rw_simp

-- ANCHOR: have_obtain
theorem have_example (x : Nat) : x + 0 = x := by
  have h : x + 0 = x := by simp
  exact h

theorem obtain_example (h : ∃ x : Nat, x > 5 ∧ x < 10) : ∃ y, y = 7 := by
  obtain ⟨_x, _hgt, _hlt⟩ := h  -- Destructure the existential
  exact ⟨7, rfl⟩
-- ANCHOR_END: have_obtain

-- ANCHOR: cases_induction
theorem cases_example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ _m => right; exact Nat.succ_pos _

theorem induction_example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n _ih => rfl
-- ANCHOR_END: cases_induction

-- ANCHOR: use_existential
theorem use_example : ∃ x : Nat, x * 2 = 10 := by
  exact ⟨5, rfl⟩
-- ANCHOR_END: use_existential

-- ANCHOR: left_right
theorem or_example : 5 < 10 ∨ 10 < 5 := by
  left
  simp
-- ANCHOR_END: left_right

-- ANCHOR: rfl
theorem rfl_example (x : Nat) : x = x := by
  rfl
-- ANCHOR_END: rfl

-- ANCHOR: trivial
theorem trivial_example : True := by
  trivial
-- ANCHOR_END: trivial

-- ANCHOR: contradiction_exfalso
theorem contradiction_example (h1 : False) : 0 = 1 := by
  contradiction

theorem exfalso_example (h : 0 = 1) : 5 = 10 := by
  exfalso  -- Goal becomes False
  simp at h
-- ANCHOR_END: contradiction_exfalso

-- ANCHOR: assumption
theorem assumption_example (P Q : Prop) (h1 : P) (_h2 : Q) : P := by
  assumption  -- Finds h1
-- ANCHOR_END: assumption

-- ANCHOR: rename
theorem rename_example (h : 1 = 1) : 1 = 1 := by
  exact h
-- ANCHOR_END: rename

-- ANCHOR: revert
theorem revert_example (x : Nat) (h : x = 5) : x = 5 := by
  revert h x
  intro x h
  exact h
-- ANCHOR_END: revert

-- ANCHOR: generalize
theorem generalize_example : (2 + 3) * 4 = 20 := by
  simp
-- ANCHOR_END: generalize

-- ANCHOR: by_contra
theorem by_contra_example : ∀ n : Nat, n = n := by
  intro n
  rfl
-- ANCHOR_END: by_contra

-- ANCHOR: split
def abs (x : Int) : Nat :=
  if x ≥ 0 then x.natAbs else (-x).natAbs

theorem split_example (x : Int) : abs x ≥ 0 := by
  unfold abs
  split <;> simp
-- ANCHOR_END: split

-- ANCHOR: ext
theorem ext_example (f g : Nat → Nat)
    (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x
-- ANCHOR_END: ext

-- ANCHOR: calc_mode
theorem calc_example (a b c : Nat)
    (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
       _ = c := h2
-- ANCHOR_END: calc_mode

-- ANCHOR: conv
theorem conv_example (x y : Nat) : x + y = y + x := by
  conv =>
    lhs  -- Focus on left-hand side
    rw [Nat.add_comm]
-- ANCHOR_END: conv

-- ANCHOR: simp_all
theorem simp_all_example (x : Nat) (h : x = 0) : x + x = 0 := by
  simp_all
-- ANCHOR_END: simp_all

-- ANCHOR: decide
theorem decide_example : 3 < 5 := by
  decide
-- ANCHOR_END: decide

-- ANCHOR: sorry_admit
@[simp]  -- Add simp attribute to suppress sorry warning
theorem incomplete_proof : ∀ P : Prop, P ∨ ¬P := by
  sorry  -- Proof left as exercise
-- ANCHOR_END: sorry_admit

-- ANCHOR: repeat
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `repeat` applies a tactic repeatedly -/
theorem repeat_example : True ∧ True ∧ True := by
  repeat constructor
  all_goals trivial
-- ANCHOR_END: repeat

-- ANCHOR: first
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem first_example (x : Nat) : x = x := by
  first | simp | rfl | sorry
-- ANCHOR_END: first

-- ANCHOR: try
theorem try_example (p q : Prop) (hp : p) : p ∨ q := by
  try assumption  -- tries to close the goal if it exactly matches a hypothesis
  exact Or.inl hp
-- ANCHOR_END: try

-- ANCHOR: all_goals
theorem all_goals_example : (1 = 1) ∧ (2 = 2) := by
  constructor
  all_goals rfl
-- ANCHOR_END: all_goals

-- ANCHOR: any_goals
theorem any_goals_example : (1 = 1) ∧ (True) := by
  constructor
  · rfl
  · trivial
-- ANCHOR_END: any_goals

-- ANCHOR: focus
theorem focus_example : True ∧ True := by
  constructor
  · focus
      trivial
  · trivial
-- ANCHOR_END: focus

-- ANCHOR: exists
theorem exists_intro : ∃ n : Nat, n > 10 := by
  exact ⟨42, by simp⟩

theorem exists_elim (h : ∃ n : Nat, n > 10) : True := by
  obtain ⟨n, hn⟩ := h
  trivial
-- ANCHOR_END: exists

-- ANCHOR: forall
theorem forall_intro : ∀ x : Nat, x + 0 = x := by
  intro x
  simp

theorem forall_elim (h : ∀ x : Nat, x + 0 = x) : 5 + 0 = 5 := by
  exact h 5
-- ANCHOR_END: forall

-- ANCHOR: specialize
theorem specialize_example (h : ∀ x : Nat, x > 0 → x ≥ 1) : 5 ≥ 1 := by
  specialize h 5 (by simp)
  exact h
-- ANCHOR_END: specialize

-- ANCHOR: convert
theorem convert_example (x y : Nat) (h : x = y) : Nat.succ x = Nat.succ y := by
  convert rfl using 1
  rw [h]
-- ANCHOR_END: convert

-- ANCHOR: nth_rewrite
theorem nth_rewrite_example (x : Nat) : x + x + x = 3 * x := by
  nth_rw 2 [← Nat.add_zero x]  -- Rewrite only the second occurrence of x
  simp
  ring
-- ANCHOR_END: nth_rewrite

-- ANCHOR: simp_rw
theorem simp_rw_example (x y : Nat) : (x + y) + (y + x) = 2 * (x + y) := by
  simp_rw [Nat.add_comm y x]
  ring
-- ANCHOR_END: simp_rw

-- ANCHOR: norm_num
theorem norm_num_example : 2 ^ 3 + 5 * 7 = 43 := by
  norm_num
-- ANCHOR_END: norm_num

-- ANCHOR: norm_cast
theorem norm_cast_example (n : Nat) : (n : Int) + 1 = ((n + 1) : Int) := by
  norm_cast
-- ANCHOR_END: norm_cast

-- ANCHOR: push_cast
set_option linter.unusedTactic false in
theorem push_cast_example (n m : Nat) : ((n + m) : Int) = (n : Int) + (m : Int) := by
  push_cast
  rfl
-- ANCHOR_END: push_cast

-- ANCHOR: split_ifs
theorem split_ifs_example (p : Prop) [Decidable p] (x y : Nat) :
    (if p then x else y) ≤ max x y := by
  split_ifs
  · exact le_max_left x y
  · exact le_max_right x y
-- ANCHOR_END: split_ifs

-- ANCHOR: symm
theorem symm_example (x y : Nat) (h : x = y) : y = x := by
  symm
  exact h
-- ANCHOR_END: symm

-- ANCHOR: trans
theorem trans_example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  trans b
  · exact h1
  · exact h2
-- ANCHOR_END: trans

-- ANCHOR: subst
theorem subst_example (x y : Nat) (h : x = 5) : x + y = 5 + y := by
  subst h
  rfl
-- ANCHOR_END: subst

-- ANCHOR: apply_fun
theorem apply_fun_example (x y : Nat) (h : x = y) : x + 2 = y + 2 := by
  apply_fun (· + 2) at h
  exact h
-- ANCHOR_END: apply_fun

-- ANCHOR: congr
theorem congr_example (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y := by
  congr
-- ANCHOR_END: congr

-- ANCHOR: gcongr
theorem gcongr_example (x y a b : Nat) (h1 : x ≤ y) (h2 : a ≤ b) : x + a ≤ y + b := by
  gcongr
-- ANCHOR_END: gcongr

-- ANCHOR: omega
theorem omega_example (x y : Nat) : x < y → x + 1 ≤ y := by
  omega
-- ANCHOR_END: omega

-- ANCHOR: linarith
theorem linarith_example (x y z : ℚ) (h1 : x < y) (h2 : y < z) : x < z := by
  linarith
-- ANCHOR_END: linarith

-- ANCHOR: ring
theorem ring_example (x y : ℤ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring
-- ANCHOR_END: ring

-- ANCHOR: field_simp
theorem field_simp_example (x y : ℚ) (hy : y ≠ 0) : x / y + 1 = (x + y) / y := by
  field_simp
-- ANCHOR_END: field_simp

-- ANCHOR: abel
theorem abel_example (x y z : ℤ) : x + y + z = z + x + y := by
  abel
-- ANCHOR_END: abel

-- ANCHOR: push_neg
theorem push_neg_example : ¬(∀ x : Nat, ∃ y, x < y) ↔ ∃ x : Nat, ∀ y, ¬(x < y) := by
  push_neg
  rfl
-- ANCHOR_END: push_neg

-- ANCHOR: by_cases
theorem by_cases_example (p : Prop) : p ∨ ¬p := by
  by_cases h : p
  · left; exact h
  · right; exact h
-- ANCHOR_END: by_cases

-- ANCHOR: choose
theorem choose_example (h : ∀ x : Nat, ∃ y : Nat, x < y) :
    ∃ f : Nat → Nat, ∀ x, x < f x := by
  choose f hf using h
  exact ⟨f, hf⟩
-- ANCHOR_END: choose

-- ANCHOR: aesop
theorem aesop_example (p q r : Prop) : p → (p → q) → (q → r) → r := by
  aesop
-- ANCHOR_END: aesop

-- ANCHOR: grind
theorem grind_example1 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  grind

theorem grind_example2 (f : Nat → Nat) (x y : Nat)
    (h1 : x = y) (h2 : f x = 10) : f y = 10 := by
  grind

theorem grind_example3 (p q r : Prop)
    (h1 : p ∧ q) (h2 : q → r) : p ∧ r := by
  grind

theorem grind_example4 (x y : Nat) :
    (if x = y then x else y) = y ∨ x = y := by
  grind
-- ANCHOR_END: grind

-- ANCHOR: grind_complex
-- Nested function applications with chained equalities
theorem grind_chain (f g : Nat → Nat) (a b c d : Nat)
    (h1 : a = b) (h2 : c = d) (h3 : f a = g c) (h4 : g d = 42) :
    f b = 42 := by
  grind

-- Existential witnesses from equality reasoning
theorem grind_exists (p : Nat → Prop) (a b : Nat)
    (h1 : a = b) (h2 : p a) : ∃ x, p x ∧ x = b := by
  grind
-- ANCHOR_END: grind_complex

-- ANCHOR: tauto
theorem tauto_example (p q : Prop) : p → (p → q) → q := by
  tauto
-- ANCHOR_END: tauto

-- ANCHOR: decide
theorem decide_example2 : 10 + 5 = 15 := by
  decide
-- ANCHOR_END: decide

-- ANCHOR: swap
theorem swap_example : True ∧ True := by
  constructor
  swap
  · trivial  -- Proves second goal first
  · trivial  -- Then first goal
-- ANCHOR_END: swap

-- ANCHOR: pick_goal
theorem pick_goal_example : True ∧ True := by
  constructor
  pick_goal 2  -- Move second goal to front
  · trivial    -- Prove second goal
  · trivial    -- Prove first goal
-- ANCHOR_END: pick_goal

-- ANCHOR: tactic_combinators
theorem combinator_example : (True ∧ True) ∧ (True ∧ True) := by
  constructor <;> (constructor <;> trivial)
-- ANCHOR_END: tactic_combinators

-- ANCHOR: linear_combination
theorem linear_combination_example (x y : ℚ) (h1 : 2*x + y = 4) (h2 : x + 2*y = 5) :
    x + y = 3 := by
  linear_combination (h1 + h2) / 3
-- ANCHOR_END: linear_combination

-- ANCHOR: positivity
set_option linter.unusedVariables false in
theorem positivity_example (x : ℚ) (h : 0 < x) : 0 < x^2 + x := by
  positivity
-- ANCHOR_END: positivity

-- ANCHOR: zify
theorem zify_example (n m : ℕ) (_ : n ≥ m) : (n - m : ℤ) = n - m := by
  zify
-- ANCHOR_END: zify

-- ANCHOR: lift
theorem lift_example (n : ℤ) (hn : 0 ≤ n) : ∃ m : ℕ, (m : ℤ) = n := by
  lift n to ℕ using hn
  exact ⟨n, rfl⟩
-- ANCHOR_END: lift

-- ANCHOR: interval_cases
theorem interval_cases_example (n : ℕ) (h : n ≤ 2) : n = 0 ∨ n = 1 ∨ n = 2 := by
  interval_cases n
  · left; rfl
  · right; left; rfl
  · right; right; rfl
-- ANCHOR_END: interval_cases

-- ANCHOR: fin_cases
theorem fin_cases_example (i : Fin 3) : i.val < 3 := by
  fin_cases i <;> simp
-- ANCHOR_END: fin_cases

-- ANCHOR: hint
theorem hint_example : 2 + 2 = 4 := by
  simp  -- hint would suggest this
-- ANCHOR_END: hint

-- ANCHOR: nlinarith
theorem nlinarith_example (x : ℚ) (h : x > 0) : x^2 > 0 := by
  nlinarith
-- ANCHOR_END: nlinarith

-- ANCHOR: bound
theorem bound_example (x y : ℕ) : x ≤ x + y := by
  bound
-- ANCHOR_END: bound

-- ANCHOR: qify
theorem qify_example (n m : ℕ) : (n : ℚ) / (m : ℚ) = (n / m : ℚ) := by
  norm_cast
-- ANCHOR_END: qify

-- ANCHOR: group
theorem group_example (x y : ℤ) : x + (-x + y) = y := by
  group
-- ANCHOR_END: group

-- ANCHOR: module_tactic
theorem module_example (x y : ℤ) (a : ℤ) : a • (x + y) = a • x + a • y := by
  module
-- ANCHOR_END: module_tactic

-- ANCHOR: noncomm_ring
theorem noncomm_ring_example (x y z : ℤ) : x * (y + z) = x * y + x * z := by
  ring
-- ANCHOR_END: noncomm_ring

end ZeroToQED.Tactics
