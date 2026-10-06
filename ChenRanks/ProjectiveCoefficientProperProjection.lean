import ChenRanks.NormalizedProjectiveCoefficientFieldObjects
import ChenRanks.ProjectiveOriginalScalarActions

/-!
# Actual properness of the constructed coefficient-model projection

The source is the genuine polynomial projective scheme, the curve is the
genuine affine normalization of the extracted coefficient field, and the
rational map is the one already constructed from the original inclusion.
Their actual graph projection is proper by base change and its closed
image. The actual finite normalization map is proper, hence so is their
actual composite. No proper model, comparison, or properness is a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The literal properness proposition for the actual normalization of
the actual coefficient graph, with its actual projection to the curve. -/
def projectiveCoefficientProjectionProperStatement
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) : Prop := by
  let L : Type u := curveCoefficientField k h a b
  letI : Field L := IntermediateField.toField (curveCoefficientField k h a b)
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
      (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  exact IsProper (normalizedRationalGraphToCurve σX σC φ)

/-- Actual base change and closed graph-image properness are composed
with the genuinely finite native normalization projection. -/
theorem projectiveCoefficientProjection_isProper
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    projectiveCoefficientProjectionProperStatement k ι h a b hh hfinite := by
  unfold projectiveCoefficientProjectionProperStatement
  let L : Type u := curveCoefficientField k h a b
  letI : Field L := IntermediateField.toField (curveCoefficientField k h a b)
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
      (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  letI : IsProper σX := projectivePolynomialScalarMorphism_isProper k (Option ι)
  letI : LocallyOfFiniteType σC :=
    curveAffineNormalizationScalarMorphism_locallyOfFiniteType k L
  let Z := rationalGraphImage σX σC φ
  let σZ := rationalGraphScalarMorphism σX σC φ
  letI : IsIntegral Z := inferInstance
  letI : LocallyOfFiniteType σZ :=
    rationalGraphScalarMorphism_locallyOfFiniteType σX σC φ
  letI : IsFinite (actualFiniteTypeNormalizationMap Z) :=
    actualFiniteTypeNormalizationMap_isFinite Z σZ
  letI : IsProper (actualFiniteTypeNormalizationMap Z) := inferInstance
  letI : IsProper (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isProper σX σC φ
  change IsProper
    (actualFiniteTypeNormalizationMap Z ≫ rationalGraphProjectionCurve σX σC φ)
  infer_instance

end ChenRanks
