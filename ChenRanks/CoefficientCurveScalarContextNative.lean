import ChenRanks.CoefficientCurveScalarContext

/-! Native accessor identities of the actual coefficient scalar context.
These identities are proved from the genuine context constructor. They
supply no field comparison, geometric model, or separation premise. -/

noncomputable section

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

variable {d : ℕ} {τ : Type*}
  (h a : AffineArrangement.RationalFunctionField (d := d))
  (b : τ → AffineArrangement.RationalFunctionField (d := d))
  (hh : Transcendental ℂ h)
  (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
    (curveCoefficientField ℂ h a b))

/-- The actual record uses the original coefficient intermediate field. -/
theorem actualCoefficientCurveScalarContext_native_L :
    (actualCoefficientCurveScalarContext h a b hh hfinite).L =
      (curveCoefficientField ℂ h a b : Type) := rfl

/-- Its field dictionary is the native intermediate-field dictionary. -/
theorem actualCoefficientCurveScalarContext_native_field :
    (actualCoefficientCurveScalarContext h a b hh hfinite).field =
      IntermediateField.toField (curveCoefficientField ℂ h a b) := rfl

/-- Its rational-function action is the actual coefficient embedding. -/
theorem actualCoefficientCurveScalarContext_native_rationalAlgebra :
    (actualCoefficientCurveScalarContext h a b hh hfinite).rationalAlgebra =
      (curveCoefficientRatFuncMap ℂ h a b hh).toRingHom.toAlgebra := rfl

/-- Its original-field action is the actual intermediate-field inclusion. -/
theorem actualCoefficientCurveScalarContext_native_originalAlgebra :
    (actualCoefficientCurveScalarContext h a b hh hfinite).originalAlgebra =
      IntermediateField.toAlgebra (curveCoefficientField ℂ h a b) := rfl

/-- Its complex action is the actual native intermediate-field action. -/
theorem actualCoefficientCurveScalarContext_native_complexAlgebra :
    (actualCoefficientCurveScalarContext h a b hh hfinite).complexAlgebra =
      inferInstanceAs (Algebra ℂ (curveCoefficientField ℂ h a b)) := rfl

end ChenRanks
