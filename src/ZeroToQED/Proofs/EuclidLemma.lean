-- ANCHOR: euclid_lemma
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace ZeroToQED.Proofs
open Nat

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

end ZeroToQED.Proofs
-- ANCHOR_END: euclid_lemma
