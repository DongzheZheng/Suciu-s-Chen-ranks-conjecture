import Mathlib

/-!
# The binomial identity for zero-relation Koszul modules

This module proves the numerical simplification used in the homogeneous
dimension formula, including ambient dimensions zero and one.
-/

namespace ChenRanks.Koszul

/-- Pascal's identity and the adjacent-binomial identity give the exact
additive formula, without natural-number subtraction. -/
theorem zero_relation_binomial_identity (m r : ℕ) :
    m * (m + r).choose (r + 1) =
      (m + r + 1).choose (r + 2) + (r + 1) * (m + r).choose (r + 2) := by
  cases m with
  | zero =>
    simp only [zero_add, zero_mul]
    rw [Nat.choose_eq_zero_of_lt (show r + 1 < r + 2 by omega),
      Nat.choose_eq_zero_of_lt (show r < r + 2 by omega)]
    simp
  | succ m =>
    have h := Nat.choose_succ_right_eq (m + 1 + r) (r + 1)
    have hsub : m + 1 + r - (r + 1) = m := by omega
    have hinc : r + 1 + 1 = r + 2 := by omega
    rw [hsub, hinc] at h
    have hp := Nat.choose_succ_succ' (m + 1 + r) (r + 1)
    rw [hinc] at hp
    nlinarith

/-- The natural-number difference appearing in the dimension calculation. -/
theorem zero_relation_binomial_difference (m r : ℕ) :
    m * (m + r).choose (r + 1) - (m + r + 1).choose (r + 2) =
      (r + 1) * (m + r).choose (r + 2) := by
  rw [zero_relation_binomial_identity, Nat.add_sub_cancel_left]

/-- The same identity in the actual monomial-count convention. -/
theorem zero_relation_multichoose_identity (m r : ℕ) :
    m * Nat.multichoose m (r + 1) =
      Nat.multichoose m (r + 2) + (r + 1) * (m + r).choose (r + 2) := by
  rw [Nat.multichoose_eq, Nat.multichoose_eq]
  have h₁ : m + (r + 1) - 1 = m + r := by omega
  have h₂ : m + (r + 2) - 1 = m + r + 1 := by omega
  rw [h₁, h₂]
  exact zero_relation_binomial_identity m r

end ChenRanks.Koszul
