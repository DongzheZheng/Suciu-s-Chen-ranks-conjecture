import ChenRanks.ProjectiveCoefficientRationalMap
import ChenRanks.RationalGraphFunctionField
import ChenRanks.RationalGraphFieldMapFunctoriality
import ChenRanks.RationalGraphFieldMapCoordinates

/-!
# The actual proper graph projection induces the original coefficient inclusion

The actual native graph comparison and the actual polynomial-projective
comparison construct an equivalence from the graph function field to the
original polynomial fraction field over the original base.  The actual
generic graph triangle identifies the native curve-projection field map
with the actual coefficient generic arrow.  Actual fraction-ring
extensionality then proves that its transport to the original field is
precisely the original coefficient-subfield inclusion.  Neither this
projection compatibility nor a source field equivalence is an input.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-- Dominance is transported along an actual equality of actual
morphisms without rewriting a dependent native field-map expression. -/
theorem actualMorphismDominance_of_equality {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (h : f = g) (hg : IsDominant g) : IsDominant f := by
  subst f
  exact hg

/-- Actual fraction-ring extensionality extends an actual coordinate
comparison through an actual coordinate-algebra equivalence. -/
theorem fractionRingMap_eq_comp_of_actual_coordinates
    {A K L F : Type*} [CommRing A] [IsDomain A] [Field K] [Field L] [Field F]
    [Algebra A K] [Algebra A L] [IsFractionRing A K]
    (e : K ≃ₐ[A] L) (f : K →+* F) (i : L →+* F)
    (h : ∀ a : A, f (algebraMap A K a) = i (algebraMap A L a)) :
    f = i.comp e.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := A) (K := K) (L := F)
    (f1 := f) (f2 := i.comp e.toRingHom)
  intro a
  change f (algebraMap A K a) = i (e (algebraMap A K a))
  rw [h, e.commutes]

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The actual graph field is the original fraction field over its
original base action, by the two constructed actual comparisons. -/
def projectiveCoefficientGraphFunctionFieldAlgEquiv
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
    letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
      structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
    (rationalGraphImage σX σC φ).functionField ≃ₐ[k]
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
  exact (rationalGraphImageFunctionFieldAlgEquiv σX σC φ).trans
    (projectivePolynomialFunctionFieldAlgEquiv k ι)

/-- The actual native curve-projection field map, transported through
the actual graph comparison into the original fraction field.  Actual
dominance is proved from actual coordinate injectivity. -/
def projectiveCoefficientCurveFieldMap
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
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  exact (projectivePolynomialFunctionFieldAlgEquiv k ι).toRingHom.comp
    ((rationalGraphImageFunctionFieldEquiv σX σC φ).toRingHom.comp
      (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σC φ)).hom)

/-- The actual projection map is evaluated using the actual native graph
comparison. This formula follows from its actual construction. -/
theorem projectiveCoefficientCurveFieldMap_apply
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
    letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
      actualMorphismDominance_of_equality
        (rationalGraphGenericArrow σX σC φ)
        (projectiveCoefficientGenericMorphism k ι h a b hh)
        (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
        (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
    letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
      rationalGraphProjectionCurve_isDominant σX σC φ
    ∀ x : (curveAffineNormalization k L).functionField,
      projectiveCoefficientCurveFieldMap k ι h a b hh hfinite x =
        projectivePolynomialFunctionFieldAlgEquiv k ι
          (rationalGraphImageFunctionFieldEquiv σX σC φ
            (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σC φ) x)) := by
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
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  dsimp only
  intro x
  rfl

end

end ChenRanks
