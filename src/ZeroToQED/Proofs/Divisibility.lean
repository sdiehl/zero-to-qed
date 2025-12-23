-- ANCHOR: divisibility_examples
import Mathlib.Tactic

namespace ZeroToQED.Proofs

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

end ZeroToQED.Proofs
-- ANCHOR_END: divisibility_examples
