import Mathlib.Tactic
import Std.Tactic.Do
import Std.Tactic.BVDecide

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
  use 5  -- supply the witness; use tries rfl on what remains
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
  rename 1 = 1 => one_eq_one  -- rename the hypothesis by its type
  exact one_eq_one
-- ANCHOR_END: rename

-- ANCHOR: revert
theorem revert_example (x : Nat) (h : x = 5) : x = 5 := by
  revert h x
  intro x h
  exact h
-- ANCHOR_END: revert

-- ANCHOR: generalize
theorem generalize_example : (2 + 3) * 4 = 20 := by
  generalize h : 2 + 3 = n  -- replace 2 + 3 by a fresh n with h : 2 + 3 = n
  omega
-- ANCHOR_END: generalize

-- ANCHOR: by_contra
theorem by_contra_example (n : Nat) (h : ¬ n ≠ 0) : n = 0 := by
  by_contra hne  -- assume n ≠ 0 and derive False
  exact h hne
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
-- Lean accepts the declaration but warns that it rests on a hole.
-- #guard_msgs turns that warning into a checked expectation.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem incomplete_proof : ∀ P : Prop, P ∨ ¬P := by
  sorry  -- Proof left as exercise

-- The hole shows up as a dependency on the sorryAx axiom.
/-- info: 'ZeroToQED.Tactics.incomplete_proof' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms incomplete_proof
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
  first | omega | simp | rfl
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
theorem any_goals_example : (1 = 1) ∧ True := by
  constructor
  any_goals rfl  -- closes 1 = 1, skips True where rfl fails
  trivial
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

-- `lia` runs grind's linear integer arithmetic engine
theorem lia_example (x y : Int) (h1 : 2 * x + 1 = y) (h2 : y < 5) : x < 2 := by
  lia

theorem lia_minmax (a b : Nat) : min a b ≤ max a b := by
  lia
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
-- `push Not` pushes negations inward through quantifiers and connectives
theorem push_neg_example : ¬(∀ x : Nat, ∃ y, x < y) ↔ ∃ x : Nat, ∀ y, ¬(x < y) := by
  push Not
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

-- ANCHOR: grind_sym
-- `sym =>` drives grind's engine one step at a time
theorem sym_example (f : Nat → Nat) (a b : Nat)
    (hinj : ∀ x y, f x = f y → x = y) (h : f a = f b) : a = b := by
  sym =>
    instantiate
    finish
-- ANCHOR_END: grind_sym

-- ANCHOR: tauto
theorem tauto_example (p q : Prop) : p → (p → q) → q := by
  tauto
-- ANCHOR_END: tauto

-- ANCHOR: decide
theorem decide_example2 : 10 + 5 = 15 := by
  decide
-- ANCHOR_END: decide

-- ANCHOR: cbv
-- `cbv` reduces the goal by call-by-value evaluation: it unfolds definitions
-- and evaluates arguments innermost-first, the same strategy the compiler uses.
theorem cbv_map : [1, 2, 3].map (· * 2) = [2, 4, 6] := by cbv

theorem cbv_fold : (List.range 5).foldl (· + ·) 0 = 10 := by cbv

-- `decide_cbv` finishes a decidable goal using call-by-value evaluation,
-- often succeeding where plain `decide` would be slow or stack-heavy.
theorem decide_cbv_example : (List.range 100).length = 100 := by decide_cbv

-- `@[cbv_opaque]` stops `cbv` from unfolding a definition;
-- `@[cbv_eval]` supplies a rewrite rule for it instead.
@[cbv_opaque] def scale (n : Nat) : Nat := n * 1000
@[cbv_eval] theorem scale_eq (n : Nat) : scale n = n * 1000 := rfl
theorem cbv_eval_example : scale 1 + scale 2 = 3000 := by cbv
-- ANCHOR_END: cbv

-- ANCHOR: try_question
-- `try?` searches for a proof and suggests what it found
theorem try_search (xs : List Nat) (h : xs ≠ []) : 0 < xs.length := by
  try?
-- ANCHOR_END: try_question

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
  hint  -- reports the tactics that close the goal, and closes it
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
theorem qify_example (a b : ℕ) (h : a ≤ b) : (a : ℚ) ≤ b := by
  qify at h  -- move the hypothesis into ℚ where the goal lives
  exact h
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
theorem noncomm_ring_example {R : Type} [Ring R] (x y z : R) :
    x * (y + z) = x * y + x * z := by
  noncomm_ring  -- no commutativity assumed
-- ANCHOR_END: noncomm_ring

/-! ## Core tactics not covered above -/

-- ANCHOR: intros
theorem intros_example : ∀ (p q : Prop), p → q → p := by
  intros       -- introduce everything, with inaccessible names
  assumption   -- still usable by tactics that search the context
-- ANCHOR_END: intros

-- ANCHOR: rintro
theorem rintro_example (p q : Prop) : p ∧ q → q ∧ p := by
  rintro ⟨hp, hq⟩  -- intro and destructure in one step
  exact ⟨hq, hp⟩
-- ANCHOR_END: rintro

-- ANCHOR: exists_tactic
theorem exists_tactic_example : ∃ n : Nat, n > 3 := by
  exists 4  -- supplies the witness and tries trivial on the rest
-- ANCHOR_END: exists_tactic

-- ANCHOR: and_intros
theorem and_intros_example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  and_intros <;> assumption  -- split every nested ∧ at once
-- ANCHOR_END: and_intros

-- ANCHOR: nofun_nomatch
theorem nofun_example : ¬ (1 = 2) := by
  nofun  -- a function with no cases: 1 = 2 has no constructors
theorem nomatch_example (h : False) : 1 = 2 := by
  nomatch h  -- match on h with no alternatives
-- ANCHOR_END: nofun_nomatch

-- ANCHOR: refine_prime
theorem refine_prime_example (p : Prop) (hp : p) : p ∧ True := by
  refine' ⟨hp, _⟩  -- plain underscores become new goals
  trivial
-- ANCHOR_END: refine_prime

-- ANCHOR: apply_rules
theorem apply_rules_example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  apply_rules [And.intro]  -- apply the rule set repeatedly, then hypotheses
-- ANCHOR_END: apply_rules

-- ANCHOR: solve_by_elim
theorem solve_by_elim_example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  solve_by_elim  -- depth-first search using local hypotheses
theorem apply_assumption_example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  apply_assumption  -- one step of that search: apply hpq
  exact hp
-- ANCHOR_END: solve_by_elim

-- ANCHOR: infer_instance
example : Inhabited Nat := by
  infer_instance  -- exact inferInstance
-- ANCHOR_END: infer_instance

-- ANCHOR: clear
set_option linter.unusedVariables false in
theorem clear_example (p q : Prop) (hp : p) (hq : q) : p := by
  clear hq  -- drop a hypothesis the proof does not need
  exact hp
-- ANCHOR_END: clear

-- ANCHOR: clear_value
theorem clear_value_example : (let x := 5; x = 5) := by
  intro x
  -- x := 5 is a let binding; freeze it into an ordinary variable with a proof
  have hx : x = 5 := rfl
  clear_value x
  exact hx
-- ANCHOR_END: clear_value

-- ANCHOR: rename_i
theorem rename_i_example : ∀ n : Nat, n = n := by
  intro        -- introduces an inaccessible n✝
  rename_i m   -- give it a usable name
  exact rfl (a := m)
-- ANCHOR_END: rename_i

-- ANCHOR: show_change
theorem show_example (n : Nat) : n + 0 = n := by
  show n = n  -- restate the goal up to definitional unfolding
  rfl
theorem change_example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  change n = 5 at h  -- the same, applied to a hypothesis
  exact h
-- ANCHOR_END: show_change

-- ANCHOR: suffices
theorem suffices_example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  suffices h : p from hpq h  -- reduce the goal to p
  exact hp
-- ANCHOR_END: suffices

-- ANCHOR: replace
theorem replace_example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  replace hp := hpq hp  -- hp : q now; the old hp is gone
  exact hp
-- ANCHOR_END: replace

-- ANCHOR: have_variants
theorem have_prime_example (p : Prop) (hp : p) : p := by
  have' h := hp  -- have via refine', so _ makes goals
  exact h
example : Nat := by
  haveI : Inhabited Nat := ⟨0⟩  -- inlined, visible to instance search
  exact default
example : Nat := by
  letI : Inhabited Nat := ⟨0⟩   -- like haveI but keeps the value
  exact default
-- ANCHOR_END: have_variants

-- ANCHOR: let_tactic
theorem let_example : 2 + 2 = 4 := by
  let x := 2       -- a local definition whose value stays visible
  show x + x = 4
  rfl
theorem let_rec_example : 10 ≤ 100 := by
  let rec go : ∀ n : Nat, n ≤ n + 90 := fun n => by omega
  exact go 10
-- ANCHOR_END: let_tactic

-- ANCHOR: lets
theorem extract_lets_example : (let x := 5; x + 1) = 6 := by
  extract_lets x   -- hoist the let into the context as x := 5
  rfl
theorem lift_lets_example : (let x := 5; x + 1) = 6 := by
  lift_lets        -- move lets outward in the goal
  intro x
  rfl
theorem let_to_have_example : (let x := 5; x + 1) = 6 := by
  let_to_have      -- turn lets whose value is not needed into haves
  rfl
-- ANCHOR_END: lets

-- ANCHOR: expose_names
theorem expose_names_example : ∀ n : Nat, n = n := by
  intro
  expose_names  -- rename every inaccessible n✝ to something referable
  rfl
-- ANCHOR_END: expose_names

-- ANCHOR: subst_vars
theorem subst_vars_example (x : Nat) (h : x = 2) : x + x = 4 := by
  subst_vars  -- substitute every hypothesis of the form var = term
  rfl
theorem subst_eqs_example (a b : Nat) (h₁ : a = 1) (h₂ : b = a) : b = 1 := by
  subst_eqs
  rfl
-- ANCHOR_END: subst_vars

-- ANCHOR: symm_saturate
theorem symm_saturate_example (a b : Nat) (h : a = b) : b = a := by
  symm_saturate  -- adds h_symm : b = a for every symmetric hypothesis
  assumption
-- ANCHOR_END: symm_saturate

-- ANCHOR: funext_ext1
theorem funext_example : (fun n : Nat => n + 0) = (fun n => n) := by
  funext n  -- reduce equality of functions to equality at n
  rfl
theorem ext1_example (a b : Nat × Nat) (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := by
  ext1 <;> assumption  -- apply exactly one extensionality lemma
-- ANCHOR_END: funext_ext1

-- ANCHOR: rwa_erw
theorem rwa_example (a b : Nat) (h : a = b) : a + 0 = b := by
  rwa [Nat.add_zero]  -- rw, then assumption
theorem erw_example (a b : Nat) (h : a = b) : a + 0 = b := by
  erw [h, Nat.add_zero]  -- rw that unfolds definitions while matching
-- ANCHOR_END: rwa_erw

-- ANCHOR: dsimp
theorem dsimp_example (a : Nat) : (fun x => x + 0) a = a := by
  dsimp  -- only definitional rewrites, so the result is still rfl-equal
-- ANCHOR_END: dsimp

-- ANCHOR: simpa
theorem simpa_example (a : Nat) (h : a = 0) : a + 0 = 0 := by
  simpa using h  -- simp the goal and h, then close by matching
-- ANCHOR_END: simpa

-- ANCHOR: unfold_delta
def double (n : Nat) := 2 * n
theorem unfold_example : double 3 = 6 := by
  unfold double  -- replace by the equation lemma
  rfl
theorem delta_example : double 3 = 6 := by
  delta double   -- raw definitional unfolding, no equation lemmas
  rfl
-- ANCHOR_END: unfold_delta

-- ANCHOR: mod_cast
theorem exact_mod_cast_example (a b : Nat) (h : (a : Int) = b) : a = b := by
  exact_mod_cast h
theorem apply_mod_cast_example (a b : Nat) (h : (a : Int) = b) : a = b := by
  apply_mod_cast h
theorem rw_mod_cast_example (a b c : Nat) (h : b = c) : ((a + b : Nat) : Int) = a + c := by
  rw_mod_cast [h]  -- normalize casts, then rewrite with h
theorem assumption_mod_cast_example (a b : Nat) (h : (a : Int) = b) : a = b := by
  assumption_mod_cast
-- ANCHOR_END: mod_cast

-- ANCHOR: ac_rfl
theorem ac_rfl_example (a b c : Nat) : a + b + c = c + b + a := by
  ac_rfl  -- equal up to associativity and commutativity
theorem ac_nf_example (a b c : Nat) : a + b + c = c + (b + a) := by
  ac_nf   -- normalize both sides instead of closing outright
-- ANCHOR_END: ac_rfl

-- ANCHOR: eq_refl
theorem eq_refl_example : 2 + 2 = 4 := by
  eq_refl  -- exact rfl with a fast path
theorem rfl_prime_example : 2 + 2 = 4 := by
  rfl'     -- rfl with smart unfolding disabled
-- ANCHOR_END: eq_refl

-- ANCHOR: rcases
theorem rcases_example (p q r : Prop) (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by
  rcases h with ⟨hp, hq | hr⟩  -- destructure nested ∧ and ∨ in one pattern
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hr⟩
-- ANCHOR_END: rcases

-- ANCHOR: match_tactic
theorem match_example (n : Nat) : n + 0 = n := by
  match n with
  | 0 => rfl
  | k + 1 => rfl
-- ANCHOR_END: match_tactic

-- ANCHOR: fun_induction
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1
theorem fun_induction_example (n : Nat) : half n ≤ n := by
  fun_induction half n <;> omega  -- one case per equation of half
theorem fun_cases_example (n : Nat) : half n ≤ n := by
  fun_cases half n   -- the same split, without induction hypotheses
  · simp
  · simp
  · simp
    exact fun_induction_example _ |>.trans (by omega)
-- ANCHOR_END: fun_induction

-- ANCHOR: injection
theorem injection_example (a b : Nat) (h : a + 1 = b + 1) : a = b := by
  injection h  -- constructors are injective: succ a = succ b gives a = b
theorem injections_example (a b : Nat)
    (h : Nat.succ (Nat.succ a) = Nat.succ (Nat.succ b)) : a = b := by
  injections   -- repeat injection as far as it goes
-- ANCHOR_END: injection

-- ANCHOR: case
theorem case_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  case right => exact hq  -- pick a goal by its tag
  case left => exact hp
theorem case_prime_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  case' right => skip   -- case' does not require closing the goal
  exact hq              -- and that goal now comes first
  exact hp
theorem next_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  next => exact hp      -- the next goal, whatever its tag
  next => exact hq
theorem cdot_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp            -- focus on the first goal and close it
  · exact hq
-- ANCHOR_END: case

-- ANCHOR: if_tactic
theorem if_example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  if h : n = 0 then exact Or.inl h else exact Or.inr h
-- ANCHOR_END: if_tactic

-- ANCHOR: false_or_by_contra
theorem false_or_by_contra_example (p : Prop) (h : ¬¬p) : p := by
  false_or_by_contra  -- goal becomes False, with ¬p in context
  exact h (by assumption)
-- ANCHOR_END: false_or_by_contra

-- ANCHOR: classical
theorem classical_example (p : Prop) : p ∨ ¬p := by
  classical  -- make Classical.propDecidable available
  exact Classical.em p
-- ANCHOR_END: classical

-- ANCHOR: native_decide
theorem native_decide_example : 2 ^ 10 = 1024 := by
  native_decide    -- compiled evaluation, trusted via an axiom
theorem decide_kernel_example : 2 ^ 10 = 1024 := by
  decide +kernel   -- skip the elaborator, let the kernel reduce
theorem decide_cbv_pow_example : 2 ^ 10 = 1024 := by
  decide_cbv       -- reduce with the cbv evaluator
-- ANCHOR_END: native_decide

-- ANCHOR: exact_question
/--
info: Try this:
  [apply] exact List.reverse_reverse xs
-/
#guard_msgs in
theorem exact_question_example (xs : List Nat) : xs.reverse.reverse = xs := by
  exact?  -- searches the library and reports the term it found
-- ANCHOR_END: exact_question

-- ANCHOR: lia
theorem lia_parity_example (x y : Int) (h : 2 * x + 1 = 2 * y) : False := by
  lia  -- linear integer arithmetic, grind's cutsat solver on its own
-- ANCHOR_END: lia

-- ANCHOR: grobner
theorem grobner_example (x y : Int) (h : x * y = 1) (h2 : x = 1) : y = 1 := by
  grobner  -- commutative ring equalities via Gröbner bases
-- ANCHOR_END: grobner

-- ANCHOR: grind_wrappers
theorem grind_order_example (a b : Nat) (h : a ≤ b) (h2 : b ≤ a) : a = b := by
  grind_order    -- only the order solver
theorem grind_linarith_example (a b : Int) (h : a < b) : a ≤ b := by
  grind_linarith -- only the linear arithmetic solver
-- ANCHOR_END: grind_wrappers

-- ANCHOR: bv_decide
theorem bv_decide_example (x : BitVec 8) : x &&& x = x := by
  bv_decide     -- SAT solver, with the certificate replayed in Lean
theorem bv_normalize_example (x : BitVec 8) : x &&& x = x := by
  bv_normalize  -- just the preprocessing step, no SAT call
theorem bv_omega_example (x : BitVec 8) (h : x < 10) : x.toNat < 10 := by
  bv_omega      -- translate to Nat arithmetic and call omega
-- ANCHOR_END: bv_decide

-- ANCHOR: done_skip
set_option linter.unusedTactic false in
theorem done_skip_example : True := by
  skip     -- do nothing
  trivial
  done     -- assert there are no goals left
-- ANCHOR_END: done_skip

-- ANCHOR: fail_if_success
theorem fail_if_success_example : True := by
  fail_if_success (exact (0 : Nat))  -- succeed only if the tactic fails
  trivial
-- ANCHOR_END: fail_if_success

-- ANCHOR: stop_admit
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem stop_example : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · rfl
  stop        -- sorry everything from here on
  exact rfl
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admit_example : 2 + 2 = 4 := by
  admit       -- a synonym for sorry
-- ANCHOR_END: stop_admit

-- ANCHOR: guards
set_option linter.unusedTactic false in
theorem guard_example (p : Prop) (hp : p) : p := by
  guard_target = p      -- fail unless the goal is literally p
  guard_hyp hp : p      -- fail unless hp has type p
  guard_expr 1 + 1 = 2  -- check two expressions are defeq
  exact hp
-- ANCHOR_END: guards

-- ANCHOR: trace
set_option linter.unusedTactic false in
/--
info: hello
---
trace: ⊢ True
-/
#guard_msgs in
theorem trace_example : True := by
  trace "hello"  -- message in the info view
  trace_state    -- print the current goals
  trivial
-- ANCHOR_END: trace

-- ANCHOR: show_term
/--
info: Try this:
  [apply] exact Eq.refl (1 + 1)
-/
#guard_msgs in
theorem show_term_example : 1 + 1 = 2 := by
  show_term rfl  -- report the term the tactic produced
-- ANCHOR_END: show_term

-- ANCHOR: rotate
theorem rotate_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  rotate_left   -- the q goal is now first
  exact hq
  exact hp
-- ANCHOR_END: rotate

-- ANCHOR: iterate
theorem iterate_example : True ∧ True ∧ True := by
  iterate 2 constructor  -- exactly two times
  all_goals trivial
theorem repeat_prime_example : True ∧ True ∧ True := by
  repeat' constructor    -- on every goal, recursively, until none applies
theorem repeat1_example : True ∧ True ∧ True := by
  repeat1' constructor   -- the same, but fail if it never applies
-- ANCHOR_END: iterate

-- ANCHOR: solve
theorem solve_example (x : Nat) : x + 0 = x := by
  solve
  | exact Nat.zero_lt_one  -- wrong, does not close the goal
  | simp                   -- first branch that closes the goal wins
-- ANCHOR_END: solve

-- ANCHOR: transparency
theorem with_reducible_example : (2 : Nat) + 2 = 4 := by
  with_reducible decide        -- only unfold @[reducible] definitions
theorem with_unfolding_all_example : (2 : Nat) + 2 = 4 := by
  with_unfolding_all rfl       -- unfold everything, even irreducible
-- ANCHOR_END: transparency

-- ANCHOR: scoped
theorem set_option_in_example : 1 + 1 = 2 := by
  set_option maxRecDepth 100 in rfl  -- option applies to this tactic only
theorem open_in_example : (1 : Nat).succ = 2 := by
  open Nat in rfl                    -- namespace opened for this tactic only
theorem unhygienic_example : ∀ n : Nat, n = n := by
  unhygienic intro  -- the introduced name is accessible, as `a✝` would not be
  exact rfl
-- ANCHOR_END: scoped

-- ANCHOR: aux_lemma
theorem as_aux_lemma_example : 1 + 1 = 2 := by
  as_aux_lemma => rfl  -- the proof term is stored as a separate lemma
theorem run_tac_example : 1 + 1 = 2 := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))  -- run TacticM code
-- ANCHOR_END: aux_lemma

-- ANCHOR: impossible
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem impossible_example (x : Nat) : x = x + 1 := by
  impossible by      -- prove the goal cannot be proved: ¬ ∀ x, x = x + 1
    intro h
    have := h 0
    omega
-- ANCHOR_END: impossible

-- ANCHOR: decreasing
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
decreasing_by all_goals decreasing_tactic  -- the default; shown explicitly
def sumTo (n : Nat) : Nat :=
  if _h : n = 0 then 0 else n + sumTo (n - 1)
termination_by n
decreasing_by decreasing_with omega  -- clean up the goal, then run omega
-- ANCHOR_END: decreasing

-- ANCHOR: get_elem_tactic
theorem get_elem_example (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i] = xs[i] := by
  get_elem_tactic  -- the tactic that discharges xs[i] bounds, called by hand
-- ANCHOR_END: get_elem_tactic

section DoTactics
open Std.Do

-- ANCHOR: mvcgen
def addOne (n : Nat) : Id Nat := do pure (n + 1)

def twice (n : Nat) : Id Nat := do
  let a ← addOne n
  let b ← addOne a
  return b

/-- warning: The `mvcgen` tactic is experimental and still under development. Avoid using it in production projects. -/
#guard_msgs in
theorem twice_spec (n : Nat) : ⦃⌜True⌝⦄ twice n ⦃⇓ r => ⌜r = n + 2⌝⦄ := by
  mvcgen [twice, addOne]  -- generate and discharge the verification conditions

def sumList (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs do
    acc := acc + x
  return acc

/-- warning: The `mvcgen` tactic is experimental and still under development. Avoid using it in production projects. -/
#guard_msgs in
theorem sumList_spec (xs : List Nat) : ⦃⌜True⌝⦄ sumList xs ⦃⇓ r => ⌜r = xs.sum⌝⦄ := by
  mvcgen [sumList] invariants
    · ⇓⟨cur, acc⟩ => ⌜acc = cur.prefix.sum⌝  -- loop invariant over the prefix seen so far
  all_goals grind  -- the remaining conditions are plain arithmetic
-- ANCHOR_END: mvcgen

-- ANCHOR: mspec
theorem addOne_spec (n : Nat) : ⦃⌜True⌝⦄ addOne n ⦃⇓ r => ⌜r = n + 1⌝⦄ := by
  unfold addOne
  mintro -   -- enter the stateful proof mode, discard the trivial precondition
  mspec      -- apply the specification of pure
-- ANCHOR_END: mspec

-- ANCHOR: mintro
example (σs : List Type) (P Q : SPred σs) : Q ⊢ₛ P → Q := by
  mintro hq _     -- introduce stateful hypotheses by name
  massumption     -- close with one of them
example (σs : List Type) (Q : SPred σs) : Q ⊢ₛ Q := by
  mstart          -- enter proof mode explicitly (mintro does this for you)
  mintro hq
  mexact hq
-- ANCHOR_END: mintro

-- ANCHOR: mcases
example (σs : List Type) (P Q R : SPred σs) : P ∧ (Q ∨ R) ∧ (Q → R) ⊢ₛ R := by
  mintro h
  mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩  -- rcases patterns: drop P, split the ∨
  · mspecialize hqr hq
    mexact hqr
  · mexact hr
-- ANCHOR_END: mcases

-- ANCHOR: mconstructor
example (σs : List Type) (P Q : SPred σs) : P ∧ Q ⊢ₛ Q ∧ P := by
  mintro ⟨hp, hq⟩
  mconstructor      -- split the ∧ goal
  · mexact hq
  · mexact hp
example (σs : List Type) (P Q : SPred σs) : P ∧ Q ⊢ₛ Q ∧ P := by
  mintro ⟨hp, hq⟩
  mrefine ⟨hq, hp⟩  -- or build it with an anonymous constructor
example (σs : List Type) (P Q : SPred σs) : P ⊢ₛ P ∨ Q := by
  mintro hp
  mleft             -- pick a side of the ∨ (mright for the other)
  mexact hp
example (σs : List Type) (P : SPred σs) : P ⊢ₛ ∃ n : Nat, ⌜n = 1⌝ := by
  mintro _
  mexists 1         -- provide the witness
  mpure_intro       -- the remaining goal is a pure proposition
  rfl
example (σs : List Type) (P : SPred σs) : ⌜False⌝ ⊢ₛ P := by
  mintro h
  mexfalso          -- switch the goal to ⌜False⌝
  mexact h
-- ANCHOR_END: mconstructor

-- ANCHOR: mhave
example (σs : List Type) (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mhave hq : Q := by mspecialize hpq hp; mexact hpq  -- a new stateful hypothesis
  mexact hq
example (σs : List Type) (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mreplace hpq : Q := by mspecialize hpq hp; mexact hpq  -- overwrite hpq instead
  mexact hpq
-- ANCHOR_END: mhave

-- ANCHOR: mcontext
example (σs : List Type) (P Q : SPred σs) : P ∧ Q ⊢ₛ Q := by
  mintro ⟨hp, hq⟩
  mclear hp         -- drop a stateful hypothesis
  mexact hq
example (σs : List Type) (P : SPred σs) : P ⊢ₛ P ∧ P := by
  mintro hp
  mdup hp => hp'    -- duplicate one
  mconstructor
  · mexact hp
  · mexact hp'
example (σs : List Type) (P : SPred σs) : P ⊢ₛ P := by
  mintro _
  mrename_i hp      -- name an inaccessible one
  mexact hp
example (σs : List Type) (P : SPred σs) : P ⊢ₛ P := by
  mintro hp
  mrevert hp        -- move it back into the goal
  mintro hp
  mexact hp
-- ANCHOR_END: mcontext

-- ANCHOR: mpure
example (σs : List Type) (Q : SPred σs) (p : Prop) (ψ : p → ⊢ₛ Q) : ⌜p⌝ ⊢ₛ Q := by
  mintro hp
  mpure hp          -- ⌜p⌝ in the stateful context becomes hp : p in the pure one
  mexact (ψ hp)
example (σs : List Type) (p : Prop) (hp : p) : ⊢ₛ (⌜p⌝ : SPred σs) := by
  mpure_intro       -- a goal ⌜p⌝ becomes the plain goal p
  exact hp
example (σs : List Type) (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs)
    (hP : ⊢ₛ P) (hΨ : ∀ x, ⊢ₛ P → Q → Ψ x) : ⊢ₛ Q → Ψ (y + 1) := by
  mintro hq
  mspecialize_pure (hΨ (y + 1)) hP hq => hΨ'  -- specialize a pure fact with stateful ones
  mexact hΨ'
-- ANCHOR_END: mpure

-- ANCHOR: mleave
example (p : Prop) (hp : p) : (⌜True⌝ : SPred [Nat]) ⊢ₛ ⌜p⌝ := by
  mleave            -- unfold the stateful logic: the goal is now ∀ s : Nat, p
  intro _
  exact hp
set_option linter.unusedTactic false in
example (σs : List Type) (P : SPred σs) : P ⊢ₛ P := by
  mintro hp
  mstop             -- leave proof mode but keep the SPred goal as it is
  exact SPred.entails.refl _
-- ANCHOR_END: mleave

end DoTactics

-- ANCHOR: itauto
theorem itauto_example (p q : Prop) (hp : p) (hq : q) : p ∧ (q ∨ ¬p) := by
  itauto  -- intuitionistic: no excluded middle, so ¬¬p → p is out of reach
-- ANCHOR_END: itauto

end ZeroToQED.Tactics
