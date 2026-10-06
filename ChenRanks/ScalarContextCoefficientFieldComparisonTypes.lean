import ChenRanks.ScalarContextCoefficientProjection
import ChenRanks.ActualCoefficientModelPullbacks

/-! Actual original-base field comparisons of the actual coefficient
model, under the primitive dictionaries of its constructed scalar context.
The definitions instantiate the proved native comparisons; none is an
isomorphism premise supplied to a final separation theorem. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The genuine inverse original-field comparison, with the native
normalized-graph scalar action and the constructed context dictionaries. -/
def scalarContextCoefficientOriginalFieldEquivType
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) : Type :=
    let S := actualCoefficientCurveScalarContext h a b hh hfinite
    letI : Field S.L := S.field
    letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
    letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
    letI : Module (RatFunc ℂ) S.L :=
      @Algebra.toModule (RatFunc ℂ) S.L
        (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
        S.rationalAlgebra
    letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
    let σX := projectivePolynomialScalarMorphism ℂ (Option (Fin d))
    let σC := curveAffineNormalizationScalarMorphism ℂ S.L
    let φ := scalarContextCoefficientRationalMap h a b hh hfinite
    letI : LocallyOfFiniteType σC :=
      curveAffineNormalizationScalarMorphism_locallyOfFiniteType ℂ S.L
    let Z := rationalGraphImage σX σC φ
    letI : IsIntegral Z := rationalGraphImage_isIntegral σX σC φ
    let σZ := rationalGraphScalarMorphism σX σC φ
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    AffineArrangement.RationalFunctionField (d := d) ≃ₐ[ℂ]
      (actualFiniteTypeNormalization Z).functionField

/-- The genuine inverse coefficient-field comparison, preserving its
original complex scalar action under the constructed context. -/
def scalarContextCoefficientCurveFieldEquivType
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) : Type :=
    let S := actualCoefficientCurveScalarContext h a b hh hfinite
    letI : Field S.L := S.field
    letI : Algebra ℂ S.L := S.complexAlgebra
    letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
    letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
    letI : Module (RatFunc ℂ) S.L :=
      @Algebra.toModule (RatFunc ℂ) S.L
        (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
        S.rationalAlgebra
    letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
    letI : Algebra ℂ (curveAffineNormalization ℂ S.L).functionField :=
      structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism ℂ S.L)
    S.L ≃ₐ[ℂ] (curveAffineNormalization ℂ S.L).functionField

end ChenRanks
