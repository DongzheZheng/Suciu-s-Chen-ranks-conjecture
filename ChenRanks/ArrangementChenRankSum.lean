import ChenRanks.ArrangementResonanceDimensionBounds

/-! The manuscript's numerical expression uses the intrinsic native
resonance-component counts. Their proved dimension bounds turn the
apparently unbounded sum over m≥2 into this actual finite interval.
This is a right-hand-side dictionary, not a proof of a Chen-rank formula.
-/

noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The literal resonance sum from the manuscript. The index m is the
dimension of the affine vector span of the actual projective component.
-/
def actualResonanceChenRankExpression (q : ℕ) : ℕ :=
  (q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
    A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q

/-- Native component counts below dimension two vanish, so the original
range sum can be restricted to the actual dimension interval. -/
theorem actualResonanceDimensionCount_range_sum (f : ℕ → ℕ) :
    (∑ m ∈ Finset.range (Fintype.card ι + 1),
      A.singularProjectiveComponentDimensionCount m * f m) =
      ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * f m := by
  apply Eq.symm
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_range.mpr (by
      have := (Finset.mem_Icc.mp hm).2
      omega)
  · intro m hm hnot
    have hmN : m ≤ Fintype.card ι := by
      have := Finset.mem_range.mp hm
      omega
    have hm2 : m < 2 := by
      by_contra hn
      apply hnot
      exact Finset.mem_Icc.mpr ⟨by omega, hmN⟩
    rw [A.singularProjectiveComponentDimensionCount_eq_zero_of_lt_two m hm2, zero_mul]

/-- The verified finite range used by the formal comparison is exactly
the manuscript's factored expression. No Chen equality is used. -/
theorem actualResonanceChenRankExpression_eq_range (q : ℕ) :
    A.actualResonanceChenRankExpression q =
      ∑ m ∈ Finset.range (Fintype.card ι + 1),
        A.singularProjectiveComponentDimensionCount m *
          ((q - 1) * (m + q - 2).choose q) := by
  rw [A.actualResonanceDimensionCount_range_sum]
  unfold actualResonanceChenRankExpression
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

end ChenRanks.AffineArrangement
