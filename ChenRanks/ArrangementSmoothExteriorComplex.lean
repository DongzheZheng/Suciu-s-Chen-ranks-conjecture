import ChenRanks.ArrangementSmoothFormComplex
import ChenRanks.OpenSmoothExteriorDifferential

/-!
The coefficient exterior differential is specialized to the original
arrangement complement and its constructed real/imaginary basis.  No
coordinate family, basis, commuting law, or model comparison is supplied
as an input.  The native smooth-form identification, graded Leibniz law,
normalized period comparison, and group formality remain to be proved.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Actual smooth coefficients and actual constant exterior generators
for the constructed real basis of the original complex affine space. -/
abbrev ActualSmoothCoefficientExterior :=
  OpenSmoothExterior.CoefficientExterior A.actualSmoothComplementOpen (Fin d × Fin 2)

/-- Actual coefficient differentiation along the constructed original
real/imaginary basis, followed by the corresponding exterior generator. -/
def actualSmoothCoefficientExteriorDifferential :
    A.ActualSmoothCoefficientExterior →ₗ[ℂ] A.ActualSmoothCoefficientExterior :=
  OpenSmoothExterior.differential A.actualSmoothComplementOpen (complexAffineRealBasis d)

/-- Actual square zero follows from actual smooth calculus and genuine
native exterior anti-commutation, with no geometric or differential input. -/
theorem actualSmoothCoefficientExteriorDifferential_comp_eq_zero :
    A.actualSmoothCoefficientExteriorDifferential.comp
      A.actualSmoothCoefficientExteriorDifferential = 0 :=
  OpenSmoothExterior.differential_comp_eq_zero
    A.actualSmoothComplementOpen (complexAffineRealBasis d)

end ChenRanks.AffineArrangement
