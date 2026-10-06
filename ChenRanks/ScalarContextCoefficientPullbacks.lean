import ChenRanks.ScalarContextCoefficientPullbackStatements
import ChenRanks.ScalarContextCoefficientFieldSquare

/-! Actual differential pullbacks of the actual coefficient model with
the constructed scalar context. The native field square proves the
property; it is not a supplied model-pullback assumption. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The actual field-square computation gives the exact native
pullback property, expressed with the actual constructed comparisons. -/
theorem scalarContextCoefficientModelPullbackProperty
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    scalarContextCoefficientModelPullbackStatement h a b hh hfinite := by
  trace "scalar-context coefficient pullbacks: proof started"
  unfold scalarContextCoefficientModelPullbackStatement
  trace "scalar-context coefficient pullbacks: exact native statement unfolded"
  letI : IsScalarTower ℂ ℂ (AffineArrangement.RationalFunctionField (d := d)) :=
    projectivePolynomialOriginalField_selfScalarTower ℂ (Fin d)
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  letI : Field S.L := S.field
  letI : Algebra ℂ S.L := S.complexAlgebra
  letI : SMul ℂ S.L := S.complexAlgebra.toSMul
  letI : Algebra S.L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra
  letI : SMul S.L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra.toSMul
  letI : IsScalarTower ℂ S.L (AffineArrangement.RationalFunctionField (d := d)) :=
    S.originalScalarTower
  letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
  letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
  letI : Module (RatFunc ℂ) S.L :=
    @Algebra.toModule (RatFunc ℂ) S.L
      (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
      S.rationalAlgebra
  letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
  let σX := projectivePolynomialScalarMorphism ℂ (Option (Fin d))
  letI : IsProper σX := projectivePolynomialScalarMorphism_isProper ℂ (Option (Fin d))
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
  letI : IsScalarTower ℂ (curveAffineNormalization ℂ S.L).functionField
      (actualFiniteTypeNormalization Z).functionField :=
    functionFieldScalarTower_of_structure_square
      (actualNormalizationScalarMorphism Z σZ) σC f
      (normalizedRationalGraphToCurve_structure σX σC φ)
  trace "scalar-context coefficient pullbacks: native scalar and projection context built"
  let eF : (actualFiniteTypeNormalization Z).functionField ≃ₐ[ℂ]
      AffineArrangement.RationalFunctionField (d := d) :=
    (scalarContextCoefficientOriginalFieldEquiv h a b hh hfinite).symm
  let eL : (curveAffineNormalization ℂ S.L).functionField ≃ₐ[ℂ] S.L :=
    (scalarContextCoefficientCurveFieldEquiv h a b hh hfinite).symm
  have hIdentity : eF.toRingHom.comp
      (algebraMap (curveAffineNormalization ℂ S.L).functionField
        (actualFiniteTypeNormalization Z).functionField) =
      (algebraMap S.L (AffineArrangement.RationalFunctionField (d := d))).comp
        eL.toRingHom := by
    exact scalarContextCoefficient_original_field_square h a b hh hfinite
  trace "scalar-context coefficient pullbacks: actual native projection identity reused"
  exact actualCoefficientModelPullbackProperty_of_identity S.L
    (curveAffineNormalization ℂ S.L).functionField eF eL hIdentity

end ChenRanks
