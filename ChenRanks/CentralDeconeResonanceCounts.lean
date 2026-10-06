import ChenRanks.CentralDeconeIsotropicFamily
import ChenRanks.ActualArrangementRationalMaximalFamily
import ChenRanks.ArrangementSingularProjectiveComponents

/-! Genuine dimension counts in the actual central decone.
Original singular equation cups and original rational logarithmic wedges
have already proved equal kernels. Identity on the original subspaces
therefore connects their actual families. Together with the genuine
central/decone family equivalence, this proves equality of their actual
dimension-fiber cardinalities, rather than assuming a component list. -/
noncomputable section
namespace ChenRanks.AffineArrangement
open Resonance
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralDeconeResonanceCountsDecidableEq : DecidableEq ι := Classical.decEq ι

def actualEquationLogarithmicFamilyEquiv :
    OriginalMaximalIsotropicFamily A.equationQuadraticCup ≃
      A.RationalMaximalIsotropicFamily where
  toFun P := ⟨P.val,
    (A.equationQuadraticCup_maximal_iff_logarithmic P.val).mp P.property.1,
    P.property.2⟩
  invFun P := ⟨P.val,
    (A.equationQuadraticCup_maximal_iff_logarithmic P.val).mpr P.property.1,
    P.property.2⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv P := by apply Subtype.ext; rfl

variable (hcentral : ∀ H, A.offset H = 0) (i₀ : ι)

/-- The actual original rational logarithmic families are genuinely
in bijection, through the original native cup and real projection. -/
def actualCentralDeconeRationalFamilyEquiv :
    (A.actualCentralDecone hcentral i₀).RationalMaximalIsotropicFamily ≃
      A.RationalMaximalIsotropicFamily :=
  ((A.actualCentralDecone hcentral i₀).actualEquationLogarithmicFamilyEquiv.symm.trans
    (A.actualCentralDeconeIsotropicFamilyEquiv hcentral i₀)).trans
      A.actualEquationLogarithmicFamilyEquiv

theorem actualCentralDeconeRationalFamilyEquiv_finrank
    (P : (A.actualCentralDecone hcentral i₀).RationalMaximalIsotropicFamily) :
    Module.finrank ℂ (A.actualCentralDeconeRationalFamilyEquiv hcentral i₀ P).val =
      Module.finrank ℂ P.val :=
  A.actualCentralDeconeIsotropicFamilyEquiv_finrank hcentral i₀
    ((A.actualCentralDecone hcentral i₀).actualEquationLogarithmicFamilyEquiv.symm P)

/-- This is a true equivalence of dimension fibers of the true finite
families, retaining original dimensions on both sides. -/
def actualCentralDeconeDimensionFiberEquiv (m : ℕ) :
    {P : (A.actualCentralDecone hcentral i₀).RationalMaximalIsotropicFamily //
      Module.finrank ℂ P.val = m} ≃
    {P : A.RationalMaximalIsotropicFamily // Module.finrank ℂ P.val = m} where
  toFun P := ⟨A.actualCentralDeconeRationalFamilyEquiv hcentral i₀ P.val, by
    rw [A.actualCentralDeconeRationalFamilyEquiv_finrank hcentral i₀]
    exact P.property⟩
  invFun Q := ⟨(A.actualCentralDeconeRationalFamilyEquiv hcentral i₀).symm Q.val, by
    have he := A.actualCentralDeconeRationalFamilyEquiv_finrank hcentral i₀
      ((A.actualCentralDeconeRationalFamilyEquiv hcentral i₀).symm Q.val)
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans Q.property⟩
  left_inv P := by
    apply Subtype.ext
    exact (A.actualCentralDeconeRationalFamilyEquiv hcentral i₀).left_inv P.val
  right_inv Q := by
    apply Subtype.ext
    exact (A.actualCentralDeconeRationalFamilyEquiv hcentral i₀).right_inv Q.val

/-- The cardinality equality follows from the proved actual dimension
fiber bijection; neither count is defined using a Chen rank formula. -/
theorem actualCentralDecone_rationalDimensionCount (m : ℕ) :
    (A.actualCentralDecone hcentral i₀).rationalMaximalIsotropicDimensionCount m =
      A.rationalMaximalIsotropicDimensionCount m := by
  classical
  letI := A.rationalMaximalIsotropicFamilyFintype
  letI := (A.actualCentralDecone hcentral i₀).rationalMaximalIsotropicFamilyFintype
  unfold rationalMaximalIsotropicDimensionCount originalMaximalIsotropicDimensionCount
  exact Fintype.card_congr (A.actualCentralDeconeDimensionFiberEquiv hcentral i₀ m)

/-- The original native projective component dimensions and their
actual fiber counts agree for the genuine central decone. -/
theorem actualCentralDecone_singularProjectiveDimensionCount (m : ℕ) :
    (A.actualCentralDecone hcentral i₀).singularProjectiveComponentDimensionCount m =
      A.singularProjectiveComponentDimensionCount m := by
  rw [(A.actualCentralDecone hcentral i₀).singularProjectiveComponentDimensionCount_eq_rational,
    A.singularProjectiveComponentDimensionCount_eq_rational]
  exact A.actualCentralDecone_rationalDimensionCount hcentral i₀ m

end ChenRanks.AffineArrangement
