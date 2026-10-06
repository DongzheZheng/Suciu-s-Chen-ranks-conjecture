import ChenRanks.CentralDeconeResonanceCounts
import ChenRanks.ArrangementResonanceDimensionBounds

/-! The same actual component sum for the original central arrangement
and its genuine affine decone. The last dimension fiber vanishes by the
true ambient dimension of the decone, rather than by an assumed rank
formula. This supplies the exact numerical sum interface for the
manuscript's central reduction. -/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralDeconeResonanceSummationDecidableEq : DecidableEq ι := Classical.decEq ι
variable (hcentral : ∀ H, A.offset H = 0) (i₀ : ι)

include hcentral i₀ in
theorem actualCentral_singularProjectiveDimensionCount_last_eq_zero :
    A.singularProjectiveComponentDimensionCount (Fintype.card ι) = 0 := by
  rw [← A.actualCentralDecone_singularProjectiveDimensionCount hcentral i₀]
  apply (A.actualCentralDecone hcentral i₀).singularProjectiveComponentDimensionCount_eq_zero_of_card_lt
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  rw [A.actualCentralDecone_card i₀]
  omega

theorem actualCentralDecone_resonanceWeightedSum (f : ℕ → ℕ) :
    (∑ m ∈ Finset.range (Fintype.card (A.ActualCentralDeconeLabels i₀) + 1),
      (A.actualCentralDecone hcentral i₀).singularProjectiveComponentDimensionCount m * f m) =
    ∑ m ∈ Finset.range (Fintype.card ι + 1),
      A.singularProjectiveComponentDimensionCount m * f m := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hc : Fintype.card (A.ActualCentralDeconeLabels i₀) + 1 = Fintype.card ι := by
    rw [A.actualCentralDecone_card i₀]
    omega
  rw [hc, Finset.sum_range_succ,
    A.actualCentral_singularProjectiveDimensionCount_last_eq_zero hcentral i₀,
    zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [A.actualCentralDecone_singularProjectiveDimensionCount hcentral i₀ m]

end ChenRanks.AffineArrangement
