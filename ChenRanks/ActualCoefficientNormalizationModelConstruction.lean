import ChenRanks.CoefficientNormalizationModel
import ChenRanks.ProjectiveCoefficientProperProjection
import ChenRanks.CurveAffineNormalizationCompact
import ChenRanks.ScalarContextCoefficientRationalMap
import ChenRanks.ScalarContextCoefficientProjection
import ChenRanks.ScalarContextCoefficientPullbacks

/-!
# Construction of the actual coefficient model bundle

The field and every scheme here come from the original coefficients.
The only mathematical inputs are the actual transcendental coefficient
and the actual finite coefficient-field extension. In particular, no
model, comparison, properness or differential pullback is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The actual graph and its actual finite normalization fill every
field of the coefficient-model record, using the already proved native
function-field square and native differential naturality. -/
def actualCoefficientNormalizationModel
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    CoefficientNormalizationModel d (actualCoefficientCurveScalarContext h a b hh hfinite) := by
  letI : Module ℂ (AffineArrangement.RationalFunctionField (d := d)) :=
    projectivePolynomialOriginalFieldModule ℂ (Fin d)
  letI : IsScalarTower ℂ ℂ (AffineArrangement.RationalFunctionField (d := d)) :=
    projectivePolynomialOriginalField_selfScalarTower ℂ (Fin d)
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  let L : Type := S.L
  letI : Field L := S.field
  letI : Algebra ℂ L := S.complexAlgebra
  letI : SMul ℂ L := S.complexAlgebra.toSMul
  letI : Module ℂ L :=
    @Algebra.toModule ℂ L
      (inferInstanceAs (CommSemiring ℂ)) (inferInstanceAs (Semiring L))
      S.complexAlgebra
  letI : Algebra L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra
  letI : SMul L (AffineArrangement.RationalFunctionField (d := d)) :=
    S.originalAlgebra.toSMul
  letI : Module L (AffineArrangement.RationalFunctionField (d := d)) :=
    @Algebra.toModule L (AffineArrangement.RationalFunctionField (d := d))
      (inferInstanceAs (CommSemiring L))
      (inferInstanceAs (Semiring (AffineArrangement.RationalFunctionField (d := d))))
      S.originalAlgebra
  letI : IsScalarTower ℂ L (AffineArrangement.RationalFunctionField (d := d)) :=
    S.originalScalarTower
  letI : Algebra (RatFunc ℂ) L := S.rationalAlgebra
  letI : SMul (RatFunc ℂ) L := S.rationalAlgebra.toSMul
  letI : Module (RatFunc ℂ) L :=
    @Algebra.toModule (RatFunc ℂ) L
      (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring L))
      S.rationalAlgebra
  letI : FiniteDimensional (RatFunc ℂ) L := S.rationalFinite
  trace "actual coefficient model bundle: constructed scalar context reused"
  let σX := projectivePolynomialScalarMorphism ℂ (Option (Fin d))
  letI : IsProper σX := projectivePolynomialScalarMorphism_isProper ℂ (Option (Fin d))
  let C := curveAffineNormalization ℂ L
  letI : IsIntegral C := curveAffineNormalization_isIntegral ℂ L
  letI : CompactSpace C := curveAffineNormalization_compactSpace ℂ L
  let σC := curveAffineNormalizationScalarMorphism ℂ L
  letI : LocallyOfFiniteType σC :=
    curveAffineNormalizationScalarMorphism_locallyOfFiniteType ℂ L
  trace "actual coefficient model bundle: actual affine curve constructed"
  let φ := scalarContextCoefficientRationalMap h a b hh hfinite
  trace "actual coefficient model bundle: native coefficient rational map reused"
  let Z := rationalGraphImage σX σC φ
  trace "actual coefficient model bundle: native graph image defined"
  let σZ := rationalGraphScalarMorphism σX σC φ
  letI : IsIntegral Z := rationalGraphImage_isIntegral σX σC φ
  trace "actual coefficient model bundle: native graph integrality reused"
  letI : LocallyOfFiniteType σZ :=
    rationalGraphScalarMorphism_locallyOfFiniteType σX σC φ
  trace "actual coefficient model bundle: actual graph constructed"
  let f := normalizedRationalGraphToCurve σX σC φ
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    scalarContextCoefficientGraphGenericArrow_isDominant h a b hh hfinite
  trace "actual coefficient model bundle: native generic arrow dominance reused"
  letI : IsDominant f := normalizedRationalGraphToCurve_isDominant σX σC φ
  trace "actual coefficient model bundle: native normalized projection dominance reused"
  letI : IsProper f :=
    normalizedRationalGraphToCurve_isProper σX σC φ
  trace "actual coefficient model bundle: actual projection dominant and proper"
  letI : Algebra ℂ C.functionField := structureFunctionFieldAlgebra σC
  letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
    structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
  letI : Algebra C.functionField (actualFiniteTypeNormalization Z).functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ C.functionField (actualFiniteTypeNormalization Z).functionField :=
    functionFieldScalarTower_of_structure_square
      (actualNormalizationScalarMorphism Z σZ) σC f
      (normalizedRationalGraphToCurve_structure σX σC φ)
  trace "actual coefficient model bundle: actual function-field scalar actions constructed"
  refine
    { Y := C
      integralY := inferInstance
      compactY := inferInstance
      Z := Z
      integralZ := inferInstance
      σZ := σZ
      finiteTypeZ := inferInstance
      σY := σC
      f := f
      dominantF := inferInstance
      properF := inferInstance
      structure_eq := normalizedRationalGraphToCurve_structure σX σC φ
      originalFieldEquiv :=
        scalarContextCoefficientOriginalFieldEquiv h a b hh hfinite
      curveFieldEquiv :=
        scalarContextCoefficientCurveFieldEquiv h a b hh hfinite
      pullbackProperty := ?_ }
  trace "actual coefficient model bundle: actual comparison data constructed"
  exact scalarContextCoefficientModelPullbackProperty h a b hh hfinite

end ChenRanks
