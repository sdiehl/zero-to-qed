import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace ZeroToQED.Mathematics

open Nat

-- ANCHOR: infinitude_primes
theorem exists_prime_factor (n : ℕ) (hn : 2 ≤ n) : ∃ p, Nat.Prime p ∧ p ∣ n := by
  by_cases hp : Nat.Prime n
  · exact ⟨n, hp, dvd_refl n⟩
  · obtain ⟨m, hm_dvd, hm_ne_one, hm_ne_n⟩ := exists_dvd_of_not_prime hn hp
    have hm_lt : m < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm_dvd) hm_ne_n
    have hm_ge : 2 ≤ m := by
      rcases m with _ | _ | m <;> simp_all
    obtain ⟨p, hp_prime, hp_dvd⟩ := exists_prime_factor m hm_ge
    exact ⟨p, hp_prime, dvd_trans hp_dvd hm_dvd⟩
termination_by n

theorem factorial_pos (n : ℕ) : 0 < n ! := Nat.factorial_pos n

theorem dvd_factorial {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) : k ∣ n ! :=
  Nat.dvd_factorial hk hkn

theorem InfinitudeOfPrimes : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have hN : 2 ≤ n ! + 1 := by
    have hfact : 0 < n ! := factorial_pos n
    omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := exists_prime_factor (n ! + 1) hN
  refine ⟨p, ?_, hp_prime⟩
  by_contra hle
  push_neg at hle
  have hp_pos : 0 < p := hp_prime.pos
  have hdvd_fact : p ∣ n ! := dvd_factorial hp_pos hle
  have hdvd_one : p ∣ 1 := (Nat.dvd_add_right hdvd_fact).mp hp_dvd
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd one_pos hdvd_one
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  omega
-- ANCHOR_END: infinitude_primes

-- ANCHOR: sqrt2_irrational
theorem sq_even_of_even {n : ℤ} (h : Even n) : Even (n ^ 2) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨2 * k ^ 2, by rw [hk]; ring⟩

theorem sq_odd_of_odd {n : ℤ} (h : Odd n) : Odd (n ^ 2) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨2 * k ^ 2 + 2 * k, by rw [hk]; ring⟩

theorem even_of_sq_even {n : ℤ} (h : Even (n ^ 2)) : Even n := by
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  have hsq_odd : Odd (n ^ 2) := sq_odd_of_odd hodd
  obtain ⟨k, hk⟩ := hsq_odd
  obtain ⟨m, hm⟩ := h
  omega

theorem sqrt2_irrational : Irrational (Real.sqrt 2) := irrational_sqrt_two
-- ANCHOR_END: sqrt2_irrational

-- ANCHOR: euclid_lemma
theorem euclid_lemma {a b p : ℕ} (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.gcd_pos_of_pos_left a hp.pos).ne')
    with hcop | hncop
  · right
    have key : p ∣ Nat.gcd (p * b) (a * b) := Nat.dvd_gcd (dvd_mul_right p b) h
    rwa [Nat.gcd_mul_right, hcop.symm, one_mul] at key
  · left
    have hdvd := Nat.gcd_dvd_left p a
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp_eq
    · omega
    · have : p ∣ a := by rw [← hp_eq]; exact Nat.gcd_dvd_right p a
      exact this

theorem prime_divides_product_iff {p a b : ℕ} (hp : Nat.Prime p) :
    p ∣ a * b ↔ p ∣ a ∨ p ∣ b :=
  ⟨euclid_lemma hp, fun h => h.elim (dvd_mul_of_dvd_left · b) (dvd_mul_of_dvd_right · a)⟩
-- ANCHOR_END: euclid_lemma

-- ANCHOR: binomial_theorem
theorem binomial_theorem (x y : ℝ) (n : ℕ) :
    (x + y) ^ n = (Finset.range (n + 1)).sum fun k => ↑(n.choose k) * x ^ k * y ^ (n - k) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intros k _
  ring

theorem binomial_two (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring

theorem binomial_three (x : ℝ) : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring

example : (2 : ℝ) ^ 5 = 32 := by norm_num
-- ANCHOR_END: binomial_theorem

-- ANCHOR: fibonacci
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem fib_add_two (n : ℕ) : fib (n + 2) = fib (n + 1) + fib n := rfl

theorem fib_pos {n : ℕ} (h : 0 < n) : 0 < fib n := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => decide
    | succ m =>
      rw [fib_add_two]
      exact Nat.add_pos_left (fib_pos (Nat.zero_lt_succ _)) _

theorem fib_sum (n : ℕ) : (Finset.range n).sum fib + 1 = fib (n + 1) := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, add_comm (fib n) 1, ← add_assoc, ih]
    rfl

-- The smallest number expressible as the sum of two cubes in two different ways.
-- Hardy found it dull; Ramanujan saw its soul.
def taxicab : ℕ := 1729
theorem hardy_ramanujan : 1^3 + 12^3 = taxicab ∧ 9^3 + 10^3 = taxicab := by decide
-- ANCHOR_END: fibonacci

-- ANCHOR: pigeonhole
theorem pigeonhole {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ a₁ a₂ : α, a₁ ≠ a₂ ∧ f a₁ = f a₂ := by
  by_contra hinj
  push_neg at hinj
  have inj : Function.Injective f := fun a₁ a₂ heq =>
    Classical.byContradiction fun hne => hinj a₁ a₂ hne heq
  exact Nat.not_lt.mpr (Fintype.card_le_of_injective f inj) h

theorem birthday_pigeonhole {n : ℕ} (hn : 365 < n) (birthday : Fin n → Fin 365) :
    ∃ i j : Fin n, i ≠ j ∧ birthday i = birthday j := by
  have hcard : Fintype.card (Fin 365) < Fintype.card (Fin n) := by simp [hn]
  exact pigeonhole birthday hcard
-- ANCHOR_END: pigeonhole

-- ANCHOR: divisibility_examples
example : 3 ∣ 12 := ⟨4, rfl⟩

example : ¬5 ∣ 12 := by decide

theorem dvd_refl' (n : ℕ) : n ∣ n := ⟨1, (mul_one n).symm⟩

theorem dvd_trans' {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨m, hm⟩ := hbc
  exact ⟨k * m, by rw [hm, hk, mul_assoc]⟩

theorem dvd_add' {a b c : ℕ} (hab : a ∣ b) (hac : a ∣ c) : a ∣ b + c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨m, hm⟩ := hac
  exact ⟨k + m, by rw [hk, hm, mul_add]⟩

theorem dvd_mul_right' (a b : ℕ) : a ∣ a * b := ⟨b, rfl⟩

theorem dvd_mul_left' (a b : ℕ) : b ∣ a * b := ⟨a, (mul_comm b a).symm⟩
-- ANCHOR_END: divisibility_examples

end ZeroToQED.Mathematics
