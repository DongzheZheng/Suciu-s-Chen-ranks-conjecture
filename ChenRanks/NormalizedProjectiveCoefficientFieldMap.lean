import ChenRanks.NormalizedProjectiveCoefficientFieldStatements
import ChenRanks.NormalizationFieldTransport

/-!
# The actual normalized coefficient model preserves the original inclusion

The actual native normalization and graph comparisons are composed. Native
function-field functoriality cancels the actual normalization projection.
The already proved graph-projection comparison therefore identifies the
actual normalized projection with the original coefficient-field inclusion.
No comparison, chosen model or desired compatibility is assumed.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] projectiveCoefficientRationalMap
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

/-- The actual normalized projection induces exactly the original
coefficient-field inclusion, under the two constructed comparisons.
The equality is proved by native composition and the actual graph
coordinate computation; no compatibility assumption is present. -/
theorem normalizedProjectiveCoefficientCurveFieldMap_eq_original_inclusion
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    normalizedProjectiveCoefficientCurveFieldInclusionStatement k ι h a b hh hfinite := by
  unfold normalizedProjectiveCoefficientCurveFieldInclusionStatement
  let L : Type u := curveCoefficientField k h a b
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
  let G : Scheme.{u} := rationalGraphImage σX σC φ
  let σG : G ⟶ Spec (.of k) := rationalGraphScalarMorphism σX σC φ
  letI : Algebra k G.functionField := structureFunctionFieldAlgebra σG
  let N : Scheme.{u} := normalizedRationalGraph σX σC φ
  let σN : N ⟶ Spec (.of k) := normalizedRationalGraphScalarMorphism σX σC φ
  letI : Algebra k N.functionField := structureFunctionFieldAlgebra σN
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  dsimp only
  unfold normalizedProjectiveCoefficientCurveFieldMap
    normalizedProjectiveCoefficientFunctionFieldAlgEquiv
  dsimp only
  rw [actualNormalizationAlgEquiv_transport_comp G σG
    (rationalGraphProjectionCurve σX σC φ)]
  exact projectiveCoefficientCurveFieldMap_eq_original_inclusion k ι h a b hh hfinite



end

end ChenRanks
