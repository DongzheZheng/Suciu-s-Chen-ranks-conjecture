import ChenRanks.ScalarContextCoefficientFieldComparisons

/-! The exact native field-square proposition of the genuinely constructed
coefficient model. This definition caches only its statement, including
all actual scalar actions. It is not an assumption or a proof certificate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The literal actual model projection identity under the primitive
scalar dictionaries of the constructed context. -/
def scalarContextCoefficientFieldSquareStatement
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) : Prop :=
    let S := actualCoefficientCurveScalarContext h a b hh hfinite
    letI : Field S.L := S.field
    letI : Algebra ℂ S.L := S.complexAlgebra
    letI : SMul ℂ S.L := S.complexAlgebra.toSMul
    letI : Algebra S.L (AffineArrangement.RationalFunctionField (d := d)) :=
      S.originalAlgebra
    letI : SMul S.L (AffineArrangement.RationalFunctionField (d := d)) :=
      S.originalAlgebra.toSMul
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
    let f := normalizedRationalGraphToCurve σX σC φ
    letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
      scalarContextCoefficientGraphGenericArrow_isDominant h a b hh hfinite
    letI : IsDominant f := normalizedRationalGraphToCurve_isDominant σX σC φ
    letI : Algebra ℂ (curveAffineNormalization ℂ S.L).functionField :=
      structureFunctionFieldAlgebra σC
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    letI : Algebra (curveAffineNormalization ℂ S.L).functionField
        (actualFiniteTypeNormalization Z).functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    let eF : (actualFiniteTypeNormalization Z).functionField ≃ₐ[ℂ]
        AffineArrangement.RationalFunctionField (d := d) :=
      (scalarContextCoefficientOriginalFieldEquiv h a b hh hfinite).symm
    let eL : (curveAffineNormalization ℂ S.L).functionField ≃ₐ[ℂ] S.L :=
      (scalarContextCoefficientCurveFieldEquiv h a b hh hfinite).symm
    eF.toRingHom.comp
        (algebraMap (curveAffineNormalization ℂ S.L).functionField
          (actualFiniteTypeNormalization Z).functionField) =
      (algebraMap S.L (AffineArrangement.RationalFunctionField (d := d))).comp
        eL.toRingHom

end ChenRanks
