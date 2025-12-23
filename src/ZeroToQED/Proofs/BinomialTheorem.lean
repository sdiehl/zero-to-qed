-- ANCHOR: binomial_theorem
import Mathlib.Tactic

namespace ZeroToQED.Proofs

theorem binomial_theorem (x y : ℝ) (n : ℕ) :
    (x + y) ^ n = (Finset.range (n + 1)).sum fun k => ↑(n.choose k) * x ^ k * y ^ (n - k) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intros k _
  ring

theorem binomial_two (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring

theorem binomial_three (x : ℝ) : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring

example : (2 : ℝ) ^ 5 = 32 := by norm_num

end ZeroToQED.Proofs
-- ANCHOR_END: binomial_theorem
