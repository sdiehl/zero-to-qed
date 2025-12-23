-- ANCHOR: sqrt2_irrational
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Tactic

namespace ZeroToQED.Proofs

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

end ZeroToQED.Proofs
-- ANCHOR_END: sqrt2_irrational
