import ChenRanks.ScalarContextCoefficientFieldSquareStatements
import ChenRanks.NormalizedGraphCoordinateFieldComparison
import ChenRanks.ScalarContextCoefficientGenericArrow

/-! The actual normalized projection preserves the actual original
coefficient inclusion under the constructed scalar context. No field
square or model is supplied as an assumption. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

-- Bounded elaboration depth for the literal native RingHom composition.
set_option maxRecDepth 2048 in
/-- The already proved native projection identity, with the exact
actual SC graph, normalization and field comparisons. -/
theorem scalarContextCoefficient_original_field_square
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    scalarContextCoefficientFieldSquareStatement h a b hh hfinite := by
  unfold scalarContextCoefficientFieldSquareStatement
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  letI : Field S.L := S.field
  letI : Algebra ℂ S.L := S.complexAlgebra
  letI : SMul ℂ S.L := S.complexAlgebra.toSMul
  letI : Algebra S.L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra
  letI : SMul S.L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra.toSMul
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
  trace "scalar-context coefficient field square: native scalar and projection context built"
  let eF : (actualFiniteTypeNormalization Z).functionField ≃ₐ[ℂ]
      AffineArrangement.RationalFunctionField (d := d) :=
    (scalarContextCoefficientOriginalFieldEquiv h a b hh hfinite).symm
  let eL : (curveAffineNormalization ℂ S.L).functionField ≃ₐ[ℂ] S.L :=
    (scalarContextCoefficientCurveFieldEquiv h a b hh hfinite).symm
  let B : Type := curveAffineNormalizationRing ℂ S.L
  letI : CommRing B := curveAffineNormalizationRing_commRing ℂ S.L
  letI : IsDomain B := curveAffineNormalizationRing_isDomain ℂ S.L
  letI : Algebra B S.L := curveAffineNormalizationRing_fieldAlgebra ℂ S.L
  letI : IsFractionRing B S.L := curveAffineNormalizationRing_isFractionRing ℂ S.L
  letI : Algebra B (curveAffineNormalization ℂ S.L).functionField :=
    curveAffineNormalization_functionFieldAlgebra ℂ S.L
  letI : IsFractionRing B (curveAffineNormalization ℂ S.L).functionField :=
    curveAffineNormalization_functionFieldIsFractionRing ℂ S.L
  letI : Algebra ℂ (projectivePolynomialAmbient ℂ (Option (Fin d))).functionField :=
    structureFunctionFieldAlgebra σX
  let eX : (projectivePolynomialAmbient ℂ (Option (Fin d))).functionField ≃+*
      AffineArrangement.RationalFunctionField (d := d) :=
    (projectivePolynomialFunctionFieldAlgEquiv ℂ (Fin d)).toRingEquiv
  let eB : (curveAffineNormalization ℂ S.L).functionField ≃ₐ[B] S.L :=
    curveAffineNormalizationFunctionFieldAlgEquiv ℂ S.L
  let i : S.L →+* AffineArrangement.RationalFunctionField (d := d) :=
    algebraMap S.L (AffineArrangement.RationalFunctionField (d := d))
  have hφ : rationalGraphGenericArrow σX σC φ =
      Spec.map (CommRingCat.ofHom
        (eX.symm.toRingHom.comp (i.comp (algebraMap B S.L)))) := by
    exact scalarContextCoefficientGenericArrow_eq_coordinates h a b hh hfinite
  trace "scalar-context coefficient field square: actual generic coordinate arrow reused"
  have hwhole := normalizedGraphCoordinateFieldComparison B S.L
    (AffineArrangement.RationalFunctionField (d := d)) σX σC φ eX eB i hφ
  trace "scalar-context coefficient field square: actual normalized coordinate identity derived"
  change eX.toRingHom.comp
      ((rationalGraphImageFunctionFieldEquiv σX σC φ).toRingHom.comp
        ((actualNormalizationFunctionFieldEquiv Z).toRingHom.comp
          (dominantFunctionFieldMap f).hom)) = i.comp eB.toRingHom
  exact hwhole

end ChenRanks
