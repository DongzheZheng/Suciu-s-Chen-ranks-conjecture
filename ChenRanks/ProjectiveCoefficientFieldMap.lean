import ChenRanks.ProjectiveCoefficientFieldStatements
import ChenRanks.RationalGraphOriginalFieldComparison

/-!
# The actual projection preserves the original coefficient inclusion

Only coordinate computations and their extension to the actual function
field are proved here. All actual source, curve, graph and field-map
objects are imported from the proved construction module.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] projectiveCoefficientRationalMap
attribute [local irreducible] projectiveCoefficientCurveFieldMap
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

/-- The actual generic coordinate inclusion determines the complete
native projection inclusion through the generic graph comparison. -/
theorem projectiveCoefficientCurveFieldMap_eq_original_inclusion
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    projectiveCoefficientCurveFieldInclusionStatement k ι h a b hh hfinite := by
  unfold projectiveCoefficientCurveFieldInclusionStatement
  let L : Type u := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let B : Type u := curveAffineNormalizationRing k L
  letI : CommRing B := curveAffineNormalizationRing_commRing k L
  letI : IsDomain B := curveAffineNormalizationRing_isDomain k L
  letI : Algebra B L := curveAffineNormalizationRing_fieldAlgebra k L
  letI : IsFractionRing B L := curveAffineNormalizationRing_isFractionRing k L
  let C : Scheme.{u} := curveAffineNormalization k L
  letI : IsIntegral C := curveAffineNormalization_isIntegral k L
  let K : Type u := C.functionField
  letI : Field K := inferInstanceAs (Field K)
  letI : Algebra B K := curveAffineNormalization_functionFieldAlgebra k L
  letI : IsFractionRing B K := curveAffineNormalization_functionFieldIsFractionRing k L
  let X : Scheme.{u} := projectivePolynomialAmbient k (Option ι)
  let σX : X ⟶ Spec (.of k) := projectivePolynomialScalarMorphism k (Option ι)
  let σC : curveAffineNormalization k L ⟶ Spec (.of k) :=
    curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  let eX : X.functionField ≃+* projectivePolynomialOriginalFunctionField k ι :=
    (projectivePolynomialFunctionFieldAlgEquiv k ι).toRingEquiv
  let eB : K ≃ₐ[B] L := curveAffineNormalizationFunctionFieldAlgEquiv k L
  let i : L →+* projectivePolynomialOriginalFunctionField k ι :=
    algebraMap L (projectivePolynomialOriginalFunctionField k ι)
  have hφ : rationalGraphGenericArrow σX σC φ =
      Spec.map (CommRingCat.ofHom
        (eX.symm.toRingHom.comp (i.comp (algebraMap B L)))) :=
    projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite
  have hwhole := rationalGraphOriginalFieldComparison B L
    (projectivePolynomialOriginalFunctionField k ι) σX σC φ eX eB i hφ
  dsimp only
  unfold projectiveCoefficientCurveFieldMap
  exact hwhole

/-- The already identified complete inclusion fixes the actual
normalization coordinate-ring elements. -/
theorem projectiveCoefficientCurveFieldMap_algebraMap
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    projectiveCoefficientCurveFieldCoordinatesStatement k ι h a b hh hfinite := by
  unfold projectiveCoefficientCurveFieldCoordinatesStatement
  let L : Type u := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let B : Type u := curveAffineNormalizationRing k L
  letI : CommRing B := curveAffineNormalizationRing_commRing k L
  letI : IsDomain B := curveAffineNormalizationRing_isDomain k L
  letI : Algebra B L := curveAffineNormalizationRing_fieldAlgebra k L
  letI : IsFractionRing B L := curveAffineNormalizationRing_isFractionRing k L
  let C : Scheme.{u} := curveAffineNormalization k L
  letI : IsIntegral C := curveAffineNormalization_isIntegral k L
  let K : Type u := C.functionField
  letI : Field K := inferInstanceAs (Field K)
  letI : Algebra B K := curveAffineNormalization_functionFieldAlgebra k L
  letI : IsFractionRing B K := curveAffineNormalization_functionFieldIsFractionRing k L
  dsimp only
  intro z
  have hz := congrArg
    (fun f : K →+* projectivePolynomialOriginalFunctionField k ι ↦
      f (algebraMap B K z))
    (projectiveCoefficientCurveFieldMap_eq_original_inclusion k ι h a b hh hfinite)
  exact hz.trans (congrArg
    (algebraMap L (projectivePolynomialOriginalFunctionField k ι))
    ((curveAffineNormalizationFunctionFieldAlgEquiv k L).commutes z))

/-- The actual curve-projection embedding respects the original base
scalars, with the actual curve action taken from its actual structure
morphism. -/
def projectiveCoefficientCurveFieldAlgHom
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : Algebra k (curveAffineNormalization k L).functionField :=
      structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism k L)
    (curveAffineNormalization k L).functionField →ₐ[k]
      projectivePolynomialOriginalFunctionField k ι := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  letI : Algebra k (curveAffineNormalization k L).functionField :=
    structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism k L)
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  let G : Scheme.{u} := rationalGraphImage σX σC φ
  let σG : G ⟶ Spec (.of k) := rationalGraphScalarMorphism σX σC φ
  letI : Algebra k G.functionField := structureFunctionFieldAlgebra σG
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  refine { projectiveCoefficientCurveFieldMap k ι h a b hh hfinite with commutes' := ?_ }
  intro c
  unfold projectiveCoefficientCurveFieldMap
  exact actualFieldEquiv_comp_dominantFunctionFieldMap_scalar σG σC
    (rationalGraphProjectionCurve σX σC φ)
    (rationalGraphProjectionCurve_structure σX σC φ)
    (projectiveCoefficientGraphFunctionFieldAlgEquiv k ι h a b hh hfinite) c

end

end ChenRanks
