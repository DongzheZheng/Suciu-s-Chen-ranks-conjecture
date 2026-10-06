import ChenRanks.CentralDeconeCoefficientCoordinates
import ChenRanks.CentralIsotropicZeroSum
import ChenRanks.IsotropicEmbeddingFamily
import ChenRanks.ArrangementEquationCupSeparation

/-! Genuine central/decone maximal isotropic families.
The actual zero-sum theorem and the real coordinate inverse discharge
the intermediate range condition. The original singular H² injection
discharges reflection of zero cup. Thus the resulting actual family
bijection needs only the original central arrangement and its chosen
hyperplane, and retains each actual subspace dimension. -/
noncomputable section
namespace ChenRanks.AffineArrangement
open Resonance
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralDeconeIsotropicFamilyDecidableEq : DecidableEq ι := Classical.decEq ι
variable (hcentral : ∀ H, A.offset H = 0) (i₀ : ι)

/-- The original exterior cups have exactly the same zero relation
on the genuine included decone coefficient directions. -/
theorem actualCentralDecone_relationWedge_zero_iff
    (a b : A.ActualCentralDeconeLabels i₀ → ℂ) :
    relationWedge A.equationQuadraticCup
        (A.actualCentralDeconeCoefficientInclusion i₀ a)
        (A.actualCentralDeconeCoefficientInclusion i₀ b) = 0 ↔
      relationWedge (A.actualCentralDecone hcentral i₀).equationQuadraticCup a b = 0 := by
  simpa only [relationWedge_apply, equationQuadraticCup_exteriorWedge] using
    A.actualCentralDecone_coefficientCup_zero_iff i₀ hcentral a b

include hcentral in
/-- Every actual central isotropic subspace of dimension at least two
lies in the genuine original decone coefficient range. -/
theorem actualCentralIsotropic_le_deconeCoefficientRange
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsIsotropic (relationWedge A.equationQuadraticCup) P)
    (hdim : 2 ≤ Module.finrank ℂ P) :
    P ≤ (A.actualCentralDeconeCoefficientInclusion i₀).range := by
  intro a ha
  have hs : A.actualCentralTotalCoefficient a = 0 :=
    A.actualCentralIsotropic_totalCoefficients_zero hcentral P hP hdim a ha
  exact ⟨(fun H => a H.val),
    A.actualCentralDeconeCoefficientInclusion_reconstruct i₀ a hs⟩

/-- The native actual maximal-isotropic family comparison is proved
from the original geometry. No cone/resonance-family hypothesis occurs. -/
def actualCentralDeconeIsotropicFamilyEquiv :
    OriginalMaximalIsotropicFamily
        (A.actualCentralDecone hcentral i₀).equationQuadraticCup ≃
      OriginalMaximalIsotropicFamily A.equationQuadraticCup :=
  isotropicEmbeddingFamilyEquiv
    (A.actualCentralDecone hcentral i₀).equationQuadraticCup A.equationQuadraticCup
    (A.actualCentralDeconeCoefficientInclusion i₀)
    (A.actualCentralDeconeCoefficientInclusion_injective i₀)
    (A.actualCentralDecone_relationWedge_zero_iff hcentral i₀)
    (A.actualCentralIsotropic_le_deconeCoefficientRange hcentral i₀)

theorem actualCentralDeconeIsotropicFamilyEquiv_finrank
    (P : OriginalMaximalIsotropicFamily
      (A.actualCentralDecone hcentral i₀).equationQuadraticCup) :
    Module.finrank ℂ (A.actualCentralDeconeIsotropicFamilyEquiv hcentral i₀ P).val =
      Module.finrank ℂ P.val :=
  isotropicEmbeddingFamilyEquiv_finrank
    (A.actualCentralDecone hcentral i₀).equationQuadraticCup A.equationQuadraticCup
    (A.actualCentralDeconeCoefficientInclusion i₀)
    (A.actualCentralDeconeCoefficientInclusion_injective i₀)
    (A.actualCentralDecone_relationWedge_zero_iff hcentral i₀)
    (A.actualCentralIsotropic_le_deconeCoefficientRange hcentral i₀) P

end ChenRanks.AffineArrangement
