import ChenRanks.ArrangementSingularProjectiveComponents

/-! Dimension bounds for the actual native resonance-component counts.
The index is the dimension of the actual affine vector span of a
projective component. The count is intrinsic to the native projective
scheme and is not defined using the desired Chen-rank formula. -/
noncomputable section
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem singularProjectiveComponentDimensionCount_eq_zero_of_lt_two
    (m : ℕ) (hm : m < 2) :
    A.singularProjectiveComponentDimensionCount m = 0 := by
  rw [A.singularProjectiveComponentDimensionCount_eq_rational]
  exact A.rationalMaximalIsotropicDimensionCount_eq_zero_of_lt_two m hm

theorem singularProjectiveComponentDimensionCount_eq_zero_of_card_lt
    (m : ℕ) (hm : Fintype.card ι < m) :
    A.singularProjectiveComponentDimensionCount m = 0 := by
  rw [A.singularProjectiveComponentDimensionCount_eq_rational]
  apply A.rationalMaximalIsotropicDimensionCount_eq_zero_of_finrank_lt
  rwa [Module.finrank_fintype_fun_eq_card]

end ChenRanks.AffineArrangement
