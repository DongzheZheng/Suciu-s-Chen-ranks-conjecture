import ChenRanks.NormalizedRationalGraph
import ChenRanks.ProjectiveCoefficientFieldMap

/-!
# The actual normalized coefficient model preserves the original inclusion

The native normalization projection, native graph projection and their
constructed function-field comparisons are composed.  The actual
normalization comparison is proved to cancel the native normalization
projection field map.  Consequently the actual normalized projection
to the coefficient curve induces exactly the original coefficient
subfield inclusion in the original polynomial fraction field.

The source model, its field comparison, properness and the required map
compatibility are not supplied as premises.  The coefficient field's
transcendental generator and its genuine finite-extension statement
remain the inputs of the preceding curve-construction step.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

section NativeNormalization

variable (X : Scheme.{u}) [IsIntegral X]
  {C : Scheme.{u}} [IsIntegral C]

/-- The constructed native normalization comparison cancels its actual
projection field map in every actual dominant composite. -/
theorem actualNormalizationFunctionFieldEquiv_comp_morphism
    (f : X ⟶ C) [IsDominant f] :
    (actualNormalizationFunctionFieldEquiv X).toRingHom.comp
        (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X ≫ f)).hom =
      (dominantFunctionFieldMap f).hom := by
  ext x
  have hc := dominantFunctionFieldMap_comp (actualFiniteTypeNormalizationMap X) f
  have hx := congrArg
    (fun g : C.functionField ⟶ (actualFiniteTypeNormalization X).functionField => g x) hc
  change (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X)).hom
      ((dominantFunctionFieldMap f).hom x) =
    (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X ≫ f)).hom x at hx
  change actualNormalizationFunctionFieldEquiv X
      ((dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X ≫ f)).hom x) =
    (dominantFunctionFieldMap f).hom x
  rw [← hx]
  rw [← actualNormalizationFunctionFieldEquiv_symm_eq_projection]
  exact (actualNormalizationFunctionFieldEquiv X).apply_symm_apply _

end NativeNormalization

section PolynomialCoefficientModel

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The actual finite normalization of the actual coefficient graph has
the original function field over the original scalar field. -/
def normalizedProjectiveCoefficientFunctionFieldAlgEquiv
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : Module (RatFunc k) L :=
      @Algebra.toModule (RatFunc k) L inferInstance inferInstance
        (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc k) L :=
      curveCoefficientRatFuncMap_finite k h a b hh hfinite
    let σX := projectivePolynomialScalarMorphism k (Option ι)
    let σC := curveAffineNormalizationScalarMorphism k L
    let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
    letI : Algebra k (normalizedRationalGraph σX σC φ).functionField :=
      structureFunctionFieldAlgebra (normalizedRationalGraphScalarMorphism σX σC φ)
    (normalizedRationalGraph σX σC φ).functionField ≃ₐ[k]
      projectivePolynomialOriginalFunctionField k ι := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L inferInstance inferInstance
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
    structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
  letI : Algebra k (normalizedRationalGraph σX σC φ).functionField :=
    structureFunctionFieldAlgebra (normalizedRationalGraphScalarMorphism σX σC φ)
  exact (actualNormalizationFunctionFieldAlgEquiv
    (rationalGraphImage σX σC φ) (rationalGraphScalarMorphism σX σC φ)).trans
      (projectiveCoefficientGraphFunctionFieldAlgEquiv k ι h a b hh hfinite)

/-- The actual normalized projection to the actual coefficient curve,
transported through the constructed comparison into the original field. -/
def normalizedProjectiveCoefficientCurveFieldMap
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    (curveAffineNormalization k L).functionField →+*
      projectivePolynomialOriginalFunctionField k ι := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L inferInstance inferInstance
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  let N : Scheme.{u} := normalizedRationalGraph σX σC φ
  let σN : N ⟶ Spec (.of k) := normalizedRationalGraphScalarMorphism σX σC φ
  letI : Algebra k N.functionField := structureFunctionFieldAlgebra σN
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  exact (normalizedProjectiveCoefficientFunctionFieldAlgEquiv k ι h a b hh hfinite).toRingHom.comp
    (dominantFunctionFieldMap (normalizedRationalGraphToCurve σX σC φ)).hom

end PolynomialCoefficientModel

end

end ChenRanks
