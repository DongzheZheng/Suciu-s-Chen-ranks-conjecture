import ChenRanks.CoefficientCurveScalarContext

/-! The already constructed native coefficient rational map is viewed
with the exact primitive dictionaries of the constructed scalar context.
This is a definition from the original coefficients, not a selected map
or a map-existence premise. -/

noncomputable section

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The genuine native rational map, with its actual base-square proof,
under the genuinely constructed coefficient scalar context. -/
def scalarContextCoefficientRationalMap
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    let S := actualCoefficientCurveScalarContext h a b hh hfinite
    letI : Field S.L := S.field
    letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
    letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
    letI : Module (RatFunc ℂ) S.L :=
      @Algebra.toModule (RatFunc ℂ) S.L
        (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
        S.rationalAlgebra
    letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
    {r : (projectivePolynomialAmbient ℂ (Option (Fin d))).RationalMap
        (curveAffineNormalization ℂ S.L) //
      r.compHom (curveAffineNormalizationScalarMorphism ℂ S.L) =
        (projectivePolynomialScalarMorphism ℂ (Option (Fin d))).toRationalMap} := by
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  letI : Field S.L := S.field
  letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
  letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
  letI : Module (RatFunc ℂ) S.L :=
    @Algebra.toModule (RatFunc ℂ) S.L
      (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
      S.rationalAlgebra
  letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
  exact projectiveCoefficientRationalMap ℂ (Fin d) h a b hh hfinite

end ChenRanks
