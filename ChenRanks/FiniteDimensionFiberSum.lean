import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

/-!
# Genuine finite sums grouped by their actual dimension fibers

The fibers are literal subtypes of the original finite indexing type.
Their cardinalities are derived from their actual filtered finite sets;
no dimension count or Hilbert formula is supplied as an assumption.
-/

open scoped BigOperators

namespace ChenRanks

/-- Regroup an actual finite sum by the genuine bounded natural-number
fibers of its index function. This includes the empty indexing type. -/
theorem sum_by_bounded_nat_fibers
    {α : Type*} [Fintype α] (d : α → ℕ) (N : ℕ)
    (hN : ∀ a, d a ≤ N) (f : ℕ → ℕ) :
    (∑ a, f (d a)) =
      ∑ m ∈ Finset.range (N + 1), Fintype.card {a : α // d a = m} * f m := by
  classical
  have hmap : ∀ a ∈ (Finset.univ : Finset α), d a ∈ Finset.range (N + 1) := by
    intro a _ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hN a))
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_const]
  simp only [Nat.nsmul_eq_mul, Fintype.card_subtype]

end ChenRanks
