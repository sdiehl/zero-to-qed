-- ANCHOR: pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace ZeroToQED.Proofs

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

end ZeroToQED.Proofs
-- ANCHOR_END: pigeonhole
