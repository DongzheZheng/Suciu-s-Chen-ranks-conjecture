import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic

/-!
# Finite signed threshold sums for the genuine grid winding formula

The function is the literal difference of two integer threshold
indicators. Its finite support and its sum are proved from integer
intervals, including either ordering and equal endpoints. The product
formula is the actual finite double sum. These arithmetic conclusions
do not by themselves identify any path winding with this function;
that identification must use the genuine segment argument computations.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

/-- The literal difference of two integer threshold indicators. -/
def signedIntegerThreshold (a b r : ℤ) : ℤ :=
  (if b ≤ r then 1 else 0) - (if a ≤ r then 1 else 0)

/-- Its support is genuinely finite, with no sign or endpoint-order
assumption. -/
theorem signedIntegerThreshold_support_finite (a b : ℤ) :
    (Function.support (signedIntegerThreshold a b)).Finite := by
  apply (Set.finite_Icc (min a b) (max a b)).subset
  intro r hr
  change signedIntegerThreshold a b r ≠ 0 at hr
  by_cases ha : a ≤ r
  · by_cases hb : b ≤ r
    · simp only [signedIntegerThreshold, if_pos ha, if_pos hb, sub_self] at hr
      exact (hr rfl).elim
    · exact ⟨(min_le_left a b).trans ha,
        (not_le.mp hb).le.trans (le_max_right a b)⟩
  · by_cases hb : b ≤ r
    · exact ⟨(min_le_right a b).trans hb,
        (not_le.mp ha).le.trans (le_max_left a b)⟩
    · simp only [signedIntegerThreshold, if_neg ha, if_neg hb, sub_self] at hr
      exact (hr rfl).elim

/-- The actual finitely supported threshold function. -/
def signedIntegerThresholdFinsupp (a b : ℤ) : ℤ →₀ ℤ :=
  Finsupp.ofSupportFinite (signedIntegerThreshold a b)
    (signedIntegerThreshold_support_finite a b)

@[simp] theorem signedIntegerThresholdFinsupp_apply (a b r : ℤ) :
    signedIntegerThresholdFinsupp a b r = signedIntegerThreshold a b r := rfl

private theorem signedIntegerThreshold_of_le (a b : ℤ) (hab : a ≤ b) (r : ℤ) :
    signedIntegerThreshold a b r = if r ∈ Finset.Ico a b then -1 else 0 := by
  simp only [signedIntegerThreshold, Finset.mem_Ico]
  split_ifs <;> omega

private theorem signedIntegerThreshold_of_ge (a b : ℤ) (hba : b ≤ a) (r : ℤ) :
    signedIntegerThreshold a b r = if r ∈ Finset.Ico b a then 1 else 0 := by
  simp only [signedIntegerThreshold, Finset.mem_Ico]
  split_ifs <;> omega

/-- The true finite total of the literal threshold difference is a-b.
The proof counts the actual finite integer interval and treats both
orientations. -/
theorem signedIntegerThresholdFinsupp_sum (a b : ℤ) :
    (signedIntegerThresholdFinsupp a b).sum (fun _ v => v) = a - b := by
  rcases le_total a b with hab | hba
  · have hs : (signedIntegerThresholdFinsupp a b).support ⊆ Finset.Ico a b := by
      intro r hr
      by_contra hn
      have hz : signedIntegerThresholdFinsupp a b r = 0 := by
        rw [signedIntegerThresholdFinsupp_apply, signedIntegerThreshold_of_le a b hab,
          if_neg hn]
      exact (Finsupp.mem_support_iff.mp hr) hz
    rw [Finsupp.sum_of_support_subset _ hs (fun _ v => v) (fun _ _ => rfl)]
    calc
      (∑ r ∈ Finset.Ico a b, signedIntegerThresholdFinsupp a b r) =
          ∑ _r ∈ Finset.Ico a b, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [signedIntegerThresholdFinsupp_apply, signedIntegerThreshold_of_le a b hab,
          if_pos hr]
      _ = a - b := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_neg_one]
        rw [Int.card_Ico_of_le a b hab]
        omega
  · have hs : (signedIntegerThresholdFinsupp a b).support ⊆ Finset.Ico b a := by
      intro r hr
      by_contra hn
      have hz : signedIntegerThresholdFinsupp a b r = 0 := by
        rw [signedIntegerThresholdFinsupp_apply, signedIntegerThreshold_of_ge a b hba,
          if_neg hn]
      exact (Finsupp.mem_support_iff.mp hr) hz
    rw [Finsupp.sum_of_support_subset _ hs (fun _ v => v) (fun _ _ => rfl)]
    calc
      (∑ r ∈ Finset.Ico b a, signedIntegerThresholdFinsupp a b r) =
          ∑ _r ∈ Finset.Ico b a, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [signedIntegerThresholdFinsupp_apply, signedIntegerThreshold_of_ge a b hba,
          if_pos hr]
      _ = a - b := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact Int.card_Ico_of_le b a hba

/-- The literal product of two actual threshold functions has genuine
finite support, derived from their actual individual supports. -/
theorem signedIntegerThresholdProduct_support_finite (a b c d : ℤ) :
    (Function.support (fun p : ℤ × ℤ =>
      signedIntegerThreshold a b p.1 * signedIntegerThreshold c d p.2)).Finite := by
  apply ((signedIntegerThreshold_support_finite a b).prod
    (signedIntegerThreshold_support_finite c d)).subset
  intro p hp
  exact mul_ne_zero_iff.mp hp

/-- The actual finitely supported product function. -/
def signedIntegerThresholdProductFinsupp (a b c d : ℤ) : (ℤ × ℤ) →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun p => signedIntegerThreshold a b p.1 * signedIntegerThreshold c d p.2)
    (signedIntegerThresholdProduct_support_finite a b c d)

@[simp] theorem signedIntegerThresholdProductFinsupp_apply (a b c d : ℤ) (p : ℤ × ℤ) :
    signedIntegerThresholdProductFinsupp a b c d p =
      signedIntegerThreshold a b p.1 * signedIntegerThreshold c d p.2 := rfl

/-- The genuine finite double sum factors into the true two finite
one-dimensional sums. -/
theorem signedIntegerThresholdProductFinsupp_sum (a b c d : ℤ) :
    (signedIntegerThresholdProductFinsupp a b c d).sum (fun _ v => v) =
      (a - b) * (c - d) := by
  let f := signedIntegerThresholdFinsupp a b
  let g := signedIntegerThresholdFinsupp c d
  have hs : (signedIntegerThresholdProductFinsupp a b c d).support ⊆
      f.support.product g.support := by
    intro p hp
    rw [Finset.product_eq_sprod, Finset.mem_product,
      Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    have h : f p.1 * g p.2 ≠ 0 := (Finsupp.mem_support_iff.mp hp)
    exact mul_ne_zero_iff.mp h
  rw [Finsupp.sum_of_support_subset _ hs (fun _ v => v) (fun _ _ => rfl),
    Finset.product_eq_sprod, Finset.sum_product]
  calc
    (∑ r ∈ f.support, ∑ s ∈ g.support, signedIntegerThresholdProductFinsupp a b c d (r, s)) =
        ∑ r ∈ f.support, ∑ s ∈ g.support, f r * g s := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rfl
    _ = (∑ r ∈ f.support, f r) * (∑ s ∈ g.support, g s) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    _ = (a - b) * (c - d) := by
      change f.sum (fun _ v => v) * g.sum (fun _ v => v) = _
      rw [signedIntegerThresholdFinsupp_sum, signedIntegerThresholdFinsupp_sum]

/-- The two true threshold totals give the vertical-first rectangle
area n*m, including zero and negative integer endpoints. Geometry must
still identify the actual deck discrepancy winding with this function. -/
theorem signedIntegerThresholdProductFinsupp_deck_sum (n m b : ℤ) :
    (signedIntegerThresholdProductFinsupp 0 n b (b + m)).sum (fun _ v => v) = n * m := by
  rw [signedIntegerThresholdProductFinsupp_sum]
  ring

end ChenRanks
