import ChenRanks.CurveAffineNormalization
import Mathlib.AlgebraicGeometry.RationalMap

/-!
# The actual rational map to the actual affine coefficient-field model

The source is the actual spectrum of a coordinate domain whose actual
fraction field is the original ambient field.  Its scheme function
field is compared with that field by the actual localization theorem.
The target is the actual integral-closure model constructed previously.
The generic-point morphism is induced by the actual integral-closure
inclusion and the actual coefficient-subfield inclusion.  Compatibility
with the original scalar field is proved, not supplied as an unidentified
field comparison or a desired commutative square.

This constructs a rational map.  Properness of a model of its graph,
normality of every chart of that graph, and resolution of this rational
map are not conclusions of this file.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial nonZeroDivisors

universe u

variable (A : Type u) [CommRing A] [IsDomain A]

/-- The native coordinate-ring action on the actual generic stalk. -/
instance affineCoordinateFunctionFieldAlgebra :
    Algebra A (Spec (.of A)).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of A)

/-- The actual affine generic stalk is the actual fraction ring. -/
instance affineCoordinateFunctionFieldIsFractionRing :
    IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (.of A)

variable (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]

/-- This comparison is constructed from the two actual fraction rings;
an arbitrary field isomorphism is not an input. -/
def affineCoordinateFunctionFieldEquiv :
    (Spec (.of A)).functionField ≃ₐ[A] F :=
  IsLocalization.algEquiv (nonZeroDivisors A) (Spec (.of A)).functionField F

variable (k : Type u) [Field k] [CharZero k]
  [Algebra k A] [Algebra k F] [IsScalarTower k A F] {ι : Type*}

/-- The actual target coordinate ring maps into the actual source
function field through the original coefficient-field inclusion. -/
def coefficientNormalizationGenericRingHom
    (h a : F) (b : ι → F) (hh : Transcendental k h) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    curveAffineNormalizationRing k L →+* (Spec (.of A)).functionField := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  exact (affineCoordinateFunctionFieldEquiv A F).symm.toRingHom.comp
    ((algebraMap L F).comp (algebraMap (curveAffineNormalizationRing k L) L))

omit [CharZero k] in
/-- The actual generic-point homomorphism respects the original scalars.
The actual RatFunc map is an original-base algebra homomorphism and the
source comparison fixes the actual coordinate ring. -/
theorem coefficientNormalizationGenericRingHom_scalar
    (h a : F) (b : ι → F) (hh : Transcendental k h) (c : k) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    coefficientNormalizationGenericRingHom A F k h a b hh
        (algebraMap k[X] (curveAffineNormalizationRing k L) (algebraMap k k[X] c)) =
      algebraMap A (Spec (.of A)).functionField (algebraMap k A c) := by
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
  change (affineCoordinateFunctionFieldEquiv A F).symm
      (algebraMap L F (algebraMap (curveAffineNormalizationRing k L) L
        (algebraMap k[X] (curveAffineNormalizationRing k L) (algebraMap k k[X] c)))) = _
  rw [hscalar, ← IsScalarTower.algebraMap_apply k L F,
    IsScalarTower.algebraMap_apply k A F]
  exact (affineCoordinateFunctionFieldEquiv A F).symm.commutes (algebraMap k A c)

/-- The actual generic-point morphism into the actual affine model. -/
def coefficientNormalizationGenericMorphism
    (h a : F) (b : ι → F) (hh : Transcendental k h) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    Spec (Spec (.of A)).functionField ⟶ curveAffineNormalization k L := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  exact Spec.map (CommRingCat.ofHom (coefficientNormalizationGenericRingHom A F k h a b hh))

omit [CharZero k] in
/-- The actual generic-point arrow and the actual structure morphisms
commute.  This is proved from actual coordinate ring maps. -/
theorem coefficientNormalizationGenericMorphism_structure
    (h a : F) (b : ι → F) (hh : Transcendental k h) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    coefficientNormalizationGenericMorphism A F k h a b hh ≫
        curveAffineNormalizationScalarMorphism k L =
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  dsimp [coefficientNormalizationGenericMorphism,
    curveAffineNormalizationScalarMorphism, curveAffineNormalizationToAffineLine]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp, Spec.fromSpecStalk_eq']
  change _ =
    Spec.map (CommRingCat.ofHom (algebraMap A (Spec (.of A)).functionField)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact coefficientNormalizationGenericRingHom_scalar A F k h a b hh c

/-- The actual coefficient field's proved finiteness makes the target
finite type.  The actual generic-point morphism therefore spreads out
into an actual rational map from the actual coordinate spectrum. -/
def coefficientNormalizationRationalMap
    (h a : F) (b : ι → F) (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    (Spec (.of A)).RationalMap (curveAffineNormalization k L) := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  exact Scheme.RationalMap.ofFunctionField
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (curveAffineNormalizationScalarMorphism k L)
    (coefficientNormalizationGenericMorphism A F k h a b hh)
    (coefficientNormalizationGenericMorphism_structure A F k h a b hh)

/-- The constructed rational map has precisely the actual generic arrow
arising from the original coefficient-field inclusion. -/
theorem coefficientNormalizationRationalMap_fromFunctionField
    (h a : F) (b : ι → F) (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    (coefficientNormalizationRationalMap A F k h a b hh hfinite).fromFunctionField =
      coefficientNormalizationGenericMorphism A F k h a b hh := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  exact Scheme.RationalMap.fromFunctionField_ofFunctionField
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (curveAffineNormalizationScalarMorphism k L)
    (coefficientNormalizationGenericMorphism A F k h a b hh)
    (coefficientNormalizationGenericMorphism_structure A F k h a b hh)

end

end ChenRanks
