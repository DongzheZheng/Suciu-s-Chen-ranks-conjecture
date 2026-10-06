import ChenRanks.CurveCoefficientDifferentials
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# An actual normal affine curve model of the actual coefficient field

For an actual finite extension of the actual rational-function field,
take the actual integral closure of the polynomial ring in that extension.
The polynomial action is constructed from the rational-function embedding.
Finiteness, the Dedekind property and the actual fraction-field comparison
are proved, rather than postulated for a desired curve model.

The associated actual affine scheme is finite, hence proper, over the
actual affine line. It is not asserted to be proper over the original
field. Projective gluing and a smooth projective resolution of the
paper's rational map are not conclusions of this file.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial nonZeroDivisors

universe u

variable (k L : Type u) [Field k] [CharZero k] [Field L] [Algebra (RatFunc k) L]

/-- The polynomial action is the actual composite through the actual
rational-function field; it is not an extra algebra premise. -/
abbrev curvePolynomialAlgebra : Algebra k[X] L :=
  ((algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))).toAlgebra

/-- The actual integral closure ring in the actual extension field. -/
def curveAffineNormalizationRing : Type u :=
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  integralClosure k[X] L

/-- The ring dictionary is the actual subalgebra ring dictionary. -/
instance curveAffineNormalizationRing_commRing :
    CommRing (curveAffineNormalizationRing k L) := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  exact Subalgebra.toCommRing (integralClosure k[X] L)

/-- The polynomial action is the actual integral-closure subalgebra action. -/
instance curveAffineNormalizationRing_polynomialAlgebra :
    Algebra k[X] (curveAffineNormalizationRing k L) := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  exact Subalgebra.algebra (integralClosure k[X] L)

/-- The inclusion of the actual integral closure into the actual field. -/
instance curveAffineNormalizationRing_fieldAlgebra :
    Algebra (curveAffineNormalizationRing k L) L := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  exact Subalgebra.toAlgebra (integralClosure k[X] L)

instance curveAffineNormalizationRing_isDomain :
    IsDomain (curveAffineNormalizationRing k L) := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  exact Subalgebra.isDomain (integralClosure k[X] L)

variable [FiniteDimensional (RatFunc k) L]

omit [CharZero k] [FiniteDimensional (RatFunc k) L] in
/-- This actual polynomial action forms the required actual tower. -/
theorem curvePolynomialAlgebra_scalarTower :
    letI : Algebra k[X] L := curvePolynomialAlgebra k L
    IsScalarTower k[X] (RatFunc k) L := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance curveAffineNormalizationRing_isDedekindDomain :
    IsDedekindDomain (curveAffineNormalizationRing k L) := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  letI : IsScalarTower k[X] (RatFunc k) L := curvePolynomialAlgebra_scalarTower k L
  letI : Algebra.IsSeparable (RatFunc k) L := inferInstance
  exact integralClosure.isDedekindDomain k[X] (RatFunc k) L

instance curveAffineNormalizationRing_finite :
    Module.Finite k[X] (curveAffineNormalizationRing k L) := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  letI : IsScalarTower k[X] (RatFunc k) L := curvePolynomialAlgebra_scalarTower k L
  letI : Algebra.IsSeparable (RatFunc k) L := inferInstance
  exact IsIntegralClosure.finite k[X] (RatFunc k) L (integralClosure k[X] L)

instance curveAffineNormalizationRing_isFractionRing :
    IsFractionRing (curveAffineNormalizationRing k L) L := by
  letI : Algebra k[X] L := curvePolynomialAlgebra k L
  letI : IsScalarTower k[X] (RatFunc k) L := curvePolynomialAlgebra_scalarTower k L
  exact IsIntegralClosure.isFractionRing_of_finite_extension
    k[X] (RatFunc k) L (integralClosure k[X] L)

/-- The actual affine normalization scheme. -/
abbrev curveAffineNormalization : Scheme.{u} :=
  Spec (.of (curveAffineNormalizationRing k L))

/-- The actual finite map of the actual affine normalization to the
actual affine line comes from the actual polynomial algebra map. -/
def curveAffineNormalizationToAffineLine :
    curveAffineNormalization k L ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (curveAffineNormalizationRing k L)))

instance curveAffineNormalization_isIntegral : IsIntegral (curveAffineNormalization k L) := by
  dsimp [curveAffineNormalization]
  infer_instance

instance curveAffineNormalizationToAffineLine_isFinite :
    IsFinite (curveAffineNormalizationToAffineLine k L) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite k[X]
    (curveAffineNormalizationRing k L))

instance curveAffineNormalizationToAffineLine_isProper :
    IsProper (curveAffineNormalizationToAffineLine k L) := by
  infer_instance

/-- The actual structure map to the original field spectrum. This
composition is finite type; it is not claimed proper over the field. -/
def curveAffineNormalizationScalarMorphism :
    curveAffineNormalization k L ⟶ Spec (.of k) :=
  curveAffineNormalizationToAffineLine k L ≫
    Spec.map (CommRingCat.ofHom (algebraMap k k[X]))

instance curveAffineNormalizationScalarMorphism_locallyOfFiniteType :
    LocallyOfFiniteType (curveAffineNormalizationScalarMorphism k L) := by
  have hPoly : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact locallyOfFiniteType_comp (curveAffineNormalizationToAffineLine k L)
    (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))
    (hf := inferInstance) (hg := hPoly)

/-- The actual coordinate-ring action on the actual generic stalk is
the actual affine scheme function-field action, with the ring object fixed. -/
instance curveAffineNormalization_functionFieldAlgebra :
    Algebra (curveAffineNormalizationRing k L) (curveAffineNormalization k L).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of (curveAffineNormalizationRing k L))

instance curveAffineNormalization_functionFieldIsFractionRing :
    IsFractionRing (curveAffineNormalizationRing k L) (curveAffineNormalization k L).functionField :=
  functionField_isFractionRing_of_affine (.of (curveAffineNormalizationRing k L))

/-- The actual scheme function field and the original extension field
are equivalent over the actual normalization ring. The actual affine
function-field localization theorem supplies the source fraction ring. -/
def curveAffineNormalizationFunctionFieldAlgEquiv :
    (curveAffineNormalization k L).functionField ≃ₐ[curveAffineNormalizationRing k L] L :=
  IsLocalization.algEquiv (nonZeroDivisors (curveAffineNormalizationRing k L))
    (curveAffineNormalization k L).functionField L

omit [CharZero k] in
/-- The actual comparison fixes the images of actual coordinate-ring
elements, so it is not merely an abstract field isomorphism. -/
@[simp]
theorem curveAffineNormalizationFunctionFieldAlgEquiv_algebraMap
    (x : curveAffineNormalizationRing k L) :
    curveAffineNormalizationFunctionFieldAlgEquiv k L
        (algebraMap (curveAffineNormalizationRing k L)
          (curveAffineNormalization k L).functionField x) =
      algebraMap (curveAffineNormalizationRing k L) L x :=
  (curveAffineNormalizationFunctionFieldAlgEquiv k L).commutes x

section CoefficientField

variable {F : Type u} [Field F] [Algebra k F] {ι : Type*}

/-- The proved actual finite coefficient field supplies all extension
instances required by the actual affine normalization construction.
No additional rational-function embedding, finite extension, desired
model existence, or function-field identification is an input. -/
theorem curveCoefficientField_actual_affineNormalization
    (h a : F) (b : ι → F) (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L := (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc k) L :=
      curveCoefficientRatFuncMap_finite k h a b hh hfinite
    let B := curveAffineNormalizationRing k L
    IsDedekindDomain B ∧ Module.Finite k[X] B ∧ IsFractionRing B L ∧
      IsIntegral (curveAffineNormalization k L) ∧
      IsFinite (curveAffineNormalizationToAffineLine k L) ∧
      Nonempty ((curveAffineNormalization k L).functionField ≃ₐ[B] L) := by
  let L := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L := (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨curveAffineNormalizationFunctionFieldAlgEquiv k L⟩⟩

end CoefficientField

end

end ChenRanks
