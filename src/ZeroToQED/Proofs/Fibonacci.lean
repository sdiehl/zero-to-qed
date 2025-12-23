-- ANCHOR: fibonacci
import Mathlib.Tactic

namespace ZeroToQED.Proofs

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

end ZeroToQED.Proofs
-- ANCHOR_END: fibonacci
