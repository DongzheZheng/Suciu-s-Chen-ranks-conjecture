import ChenRanks.ProjectivePolynomialFunctionField
import ChenRanks.CurveFunctionFieldScalars
import ChenRanks.RationalGraphImage
import ChenRanks.AffineGenericFieldMap

/-!
# The actual coefficient map on the actual proper polynomial ambient

The native standard-chart comparison, rather than a supplied source
field isomorphism, identifies the original polynomial fraction field
with the actual projective function field over the original base.
The actual normalization-ring inclusion and coefficient-subfield
inclusion then construct the actual generic arrow.  Its base square
and its dominance are proved from those maps.  The native rational-map
equivalence produces the actual base-compatible rational map needed
by the actual graph factory.

The finite coefficient-field extension remains an explicit structural
input.  This file does not infer that input from a resonance plane,
nor does it claim logarithmic separation or the Chen rank formula.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι]

attribute [local instance] projectivePolynomialOriginalFieldAlgebra

/-- The actual scalar action on the actual native projective function
field is constructed from its actual structure morphism. -/
abbrev projectivePolynomialActualFunctionFieldAlgebra :
    Algebra k (projectivePolynomialAmbient k (Option ι)).functionField :=
  structureFunctionFieldAlgebra (projectivePolynomialScalarMorphism k (Option ι))

attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra

variable {τ : Type*}

/-- The actual coordinate map into the actual projective generic stalk.
All three maps in this composite have been constructed from the
original coordinate field and its actual coefficient subfield. -/
def projectiveCoefficientGenericRingHom
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    curveAffineNormalizationRing k L →+*
      (projectivePolynomialAmbient k (Option ι)).functionField := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  exact (projectivePolynomialFunctionFieldAlgEquiv k ι).symm.toRingHom.comp
    ((algebraMap L (projectivePolynomialOriginalFunctionField k ι)).comp
      (algebraMap (curveAffineNormalizationRing k L) L))

omit [CharZero k] in
/-- The actual generic coordinate map fixes the original base scalars.
This uses the actual RatFunc algebra homomorphism and the proved
original-base projective function-field comparison. -/
theorem projectiveCoefficientGenericRingHom_scalar
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h) (c : k) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    projectiveCoefficientGenericRingHom k ι h a b hh
        (algebraMap k[X] (curveAffineNormalizationRing k L) (algebraMap k k[X] c)) =
      structureFunctionFieldScalarHom (projectivePolynomialScalarMorphism k (Option ι)) c := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  have hscalar :
      algebraMap (curveAffineNormalizationRing k L) L
        (algebraMap k[X] (curveAffineNormalizationRing k L) (algebraMap k k[X] c)) =
        algebraMap k L c := by
    change curveCoefficientRatFuncMap k h a b hh
      (algebraMap k[X] (RatFunc k) (algebraMap k k[X] c)) = algebraMap k L c
    rw [← IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
    exact (curveCoefficientRatFuncMap k h a b hh).commutes c
  change (projectivePolynomialFunctionFieldAlgEquiv k ι).symm
      (algebraMap L (projectivePolynomialOriginalFunctionField k ι)
        (algebraMap (curveAffineNormalizationRing k L) L
          (algebraMap k[X] (curveAffineNormalizationRing k L) (algebraMap k k[X] c)))) =
    algebraMap k (projectivePolynomialAmbient k (Option ι)).functionField c
  rw [hscalar, ← IsScalarTower.algebraMap_apply k L
    (projectivePolynomialOriginalFunctionField k ι)]
  exact (projectivePolynomialFunctionFieldAlgEquiv k ι).symm.commutes c

/-- The actual generic arrow into the actual normalization scheme. -/
def projectiveCoefficientGenericMorphism
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    Spec (projectivePolynomialAmbient k (Option ι)).functionField ⟶
      curveAffineNormalization k L := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  exact Spec.map (CommRingCat.ofHom (projectiveCoefficientGenericRingHom k ι h a b hh))

omit [CharZero k] in
/-- The actual generic arrow is over the original base.  The square
is derived by the faithful Spec functor, not supplied as an input. -/
theorem projectiveCoefficientGenericMorphism_structure
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    projectiveCoefficientGenericMorphism k ι h a b hh ≫
        curveAffineNormalizationScalarMorphism k L =
      (projectivePolynomialAmbient k (Option ι)).fromSpecStalk
        (genericPoint (projectivePolynomialAmbient k (Option ι))) ≫
          projectivePolynomialScalarMorphism k (Option ι) := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  rw [← structureFunctionFieldScalarHom_spec]
  dsimp [projectiveCoefficientGenericMorphism,
    curveAffineNormalizationScalarMorphism, curveAffineNormalizationToAffineLine]
  simp only [← Spec.map_comp, Category.assoc]
  apply congrArg Spec.map
  ext c
  exact projectiveCoefficientGenericRingHom_scalar k ι h a b hh c

omit [CharZero k] in
/-- The actual generic ring map is injective, by the actual integral
closure inclusion, actual coefficient-field inclusion and actual
projective comparison. -/
theorem projectiveCoefficientGenericRingHom_injective
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    Function.Injective (projectiveCoefficientGenericRingHom k ι h a b hh) := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L inferInstance inferInstance
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  letI : IsFractionRing (curveAffineNormalizationRing k L) L :=
    curveAffineNormalizationRing_isFractionRing k L
  exact (projectivePolynomialFunctionFieldAlgEquiv k ι).symm.injective.comp
    ((algebraMap L (projectivePolynomialOriginalFunctionField k ι)).injective.comp
      (IsFractionRing.injective (curveAffineNormalizationRing k L) L))

omit [CharZero k] in
/-- Actual coordinate injectivity proves actual generic dominance.
This is not a blanket nonconstancy assertion about rational maps. -/
theorem projectiveCoefficientGenericMorphism_isDominant
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    IsDominant (projectiveCoefficientGenericMorphism k ι h a b hh) := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  exact injectiveAffineGenericMorphism_isDominant _ _
    (projectiveCoefficientGenericRingHom k ι h a b hh)
    (projectiveCoefficientGenericRingHom_injective k ι h a b hh hfinite)

/-- The actual native equivalence spreads out the proved actual generic
arrow to an actual rational map over the original base. -/
def projectiveCoefficientRationalMap
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
    {r : (projectivePolynomialAmbient k (Option ι)).RationalMap (curveAffineNormalization k L) //
      r.compHom (curveAffineNormalizationScalarMorphism k L) =
        (projectivePolynomialScalarMorphism k (Option ι)).toRationalMap} := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L inferInstance inferInstance
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  letI : LocallyOfFiniteType (curveAffineNormalizationScalarMorphism k L) :=
    curveAffineNormalizationScalarMorphism_locallyOfFiniteType k L
  exact (Scheme.RationalMap.equivFunctionField
    (projectivePolynomialScalarMorphism k (Option ι))
    (curveAffineNormalizationScalarMorphism k L))
      ⟨projectiveCoefficientGenericMorphism k ι h a b hh,
        projectiveCoefficientGenericMorphism_structure k ι h a b hh⟩

/-- The graph factory's actual generic arrow is exactly the original
coefficient-inclusion arrow constructed above. -/
theorem projectiveCoefficientRationalMap_genericArrow
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
    letI : LocallyOfFiniteType (curveAffineNormalizationScalarMorphism k L) :=
      curveAffineNormalizationScalarMorphism_locallyOfFiniteType k L
    rationalGraphGenericArrow (projectivePolynomialScalarMorphism k (Option ι))
        (curveAffineNormalizationScalarMorphism k L)
        (projectiveCoefficientRationalMap k ι h a b hh hfinite) =
      projectiveCoefficientGenericMorphism k ι h a b hh := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L inferInstance inferInstance
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  letI : LocallyOfFiniteType (curveAffineNormalizationScalarMorphism k L) :=
    curveAffineNormalizationScalarMorphism_locallyOfFiniteType k L
  exact congrArg Subtype.val
    ((Scheme.RationalMap.equivFunctionField
      (projectivePolynomialScalarMorphism k (Option ι))
      (curveAffineNormalizationScalarMorphism k L)).symm_apply_apply
        ⟨projectiveCoefficientGenericMorphism k ι h a b hh,
          projectiveCoefficientGenericMorphism_structure k ι h a b hh⟩)

end

end ChenRanks
