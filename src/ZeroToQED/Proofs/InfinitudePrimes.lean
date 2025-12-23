-- ANCHOR: infinitude_primes
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ZeroToQED.Proofs
open Nat

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

end ZeroToQED.Proofs
-- ANCHOR_END: infinitude_primes
