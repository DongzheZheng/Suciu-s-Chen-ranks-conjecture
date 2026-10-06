import ChenRanks.ActualCoefficientNormalizationModelConstruction

/-! The final original-curve implication uses only the actual constructed
scalar/model bundles. No bundle or its existence is a theorem parameter. -/

noncomputable section

namespace ChenRanks.AffineArrangement

attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] quadraticLogarithmicRealization logarithmicRealization
attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule

variable {d : ℕ} {ι τ : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual model is constructed from the original coefficients and
the actual finite curve extension; its genuine separation consequence
then applies to the given original differential pullbacks. -/
theorem rationalQuadraticKernel_separated_of_original_curve
    (h a : RationalFunctionField (d := d))
    (b : τ → RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    A.arrangementOriginalCurveSeparationStatement h a b := by
  unfold arrangementOriginalCurveSeparationStatement
  intro P hP hpull
  unfold arrangementOriginalCurvePullbackStatement at hpull
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  let M := actualCoefficientNormalizationModel h a b hh hfinite
  exact A.rationalQuadraticKernel_separated_of_coefficient_model S M P hP hpull

end ChenRanks.AffineArrangement
