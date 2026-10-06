import ChenRanks.CurveAffineNormalization
import ChenRanks.StructureFunctionFieldTower

/-!
# Original scalar compatibility for the actual affine curve field

The scalar map of the actual normalization scheme is identified with the
actual polynomial-coordinate scalar map by the faithful Spec functor.
The previously constructed coordinate-ring fraction-field equivalence
therefore preserves the original base scalars.  In the coefficient-field
application, the actual rational-function embedding's algebra-map
identity proves compatibility with the original, already defined scalar
action on the coefficient subfield.  No compatible field equivalence is
assumed.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

universe u

variable (k L : Type u) [Field k] [CharZero k] [Field L]
  [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]

omit [CharZero k] [FiniteDimensional (RatFunc k) L] in
/-- The actual normalization scheme's scalar germ equals the actual
polynomial scalar followed by its actual coordinate-ring generic germ. -/
theorem curveAffineNormalizationFunctionField_scalar (c : k) :
    structureFunctionFieldScalarHom (curveAffineNormalizationScalarMorphism k L) c =
      algebraMap (curveAffineNormalizationRing k L)
        (curveAffineNormalization k L).functionField
          (algebraMap k[X] (curveAffineNormalizationRing k L) (algebraMap k k[X] c)) := by
  have hs : structureFunctionFieldScalarHom (curveAffineNormalizationScalarMorphism k L) =
      CommRingCat.ofHom
        ((algebraMap (curveAffineNormalizationRing k L)
            (curveAffineNormalization k L).functionField).comp
          ((algebraMap k[X] (curveAffineNormalizationRing k L)).comp (algebraMap k k[X]))) := by
    apply Spec.map_injective
    rw [structureFunctionFieldScalarHom_spec]
    dsimp [curveAffineNormalizationScalarMorphism, curveAffineNormalizationToAffineLine]
    rw [Spec.fromSpecStalk_eq']
    simp only [Spec.map_comp, Category.assoc]
    rfl
  exact congrArg (fun f : (.of k) ⟶ (curveAffineNormalization k L).functionField => f c) hs

/-- The original-base algebra structure on the extension field is
constructed through its actual rational-function embedding. -/
abbrev curveNormalizationBaseFieldAlgebra : Algebra k L :=
  ((algebraMap (RatFunc k) L).comp (algebraMap k (RatFunc k))).toAlgebra

/-- The actual scheme-field comparison is an equivalence over the
actual original base action, not just over the normalization ring. -/
def curveAffineNormalizationFunctionFieldBaseAlgEquiv :
    letI : Algebra k (curveAffineNormalization k L).functionField :=
      structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism k L)
    letI : Algebra k L := curveNormalizationBaseFieldAlgebra k L
    (curveAffineNormalization k L).functionField ≃ₐ[k] L := by
  letI : Algebra k (curveAffineNormalization k L).functionField :=
    structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism k L)
  letI : Algebra k L := curveNormalizationBaseFieldAlgebra k L
  refine { (curveAffineNormalizationFunctionFieldAlgEquiv k L).toRingEquiv with
    commutes' := ?_ }
  intro c
  change curveAffineNormalizationFunctionFieldAlgEquiv k L
      (structureFunctionFieldScalarHom (curveAffineNormalizationScalarMorphism k L) c) =
    algebraMap k L c
  rw [curveAffineNormalizationFunctionField_scalar,
    curveAffineNormalizationFunctionFieldAlgEquiv_algebraMap]
  change algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (algebraMap k k[X] c)) =
    algebraMap (RatFunc k) L (algebraMap k (RatFunc k) c)
  rw [← IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]

section CoefficientField

variable {F : Type u} [Field F] [Algebra k F] {ι : Type*}

/-- For the actual coefficient field, the actual normalization comparison
preserves its original scalar action.  This follows from the actual
rational-function map being an original-base algebra homomorphism. -/
def curveCoefficientNormalizationFunctionFieldAlgEquiv
    (h a : F) (b : ι → F) (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    let L₀ := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L₀ :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc k) L₀ :=
      curveCoefficientRatFuncMap_finite k h a b hh hfinite
    letI : Algebra k (curveAffineNormalization k L₀).functionField :=
      structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism k L₀)
    (curveAffineNormalization k L₀).functionField ≃ₐ[k] L₀ := by
  let L₀ := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L₀ :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L₀ :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  letI : Algebra k (curveAffineNormalization k L₀).functionField :=
    structureFunctionFieldAlgebra (curveAffineNormalizationScalarMorphism k L₀)
  refine { (curveAffineNormalizationFunctionFieldAlgEquiv k L₀).toRingEquiv with
    commutes' := ?_ }
  intro c
  change curveAffineNormalizationFunctionFieldAlgEquiv k L₀
      (structureFunctionFieldScalarHom (curveAffineNormalizationScalarMorphism k L₀) c) =
    algebraMap k L₀ c
  rw [curveAffineNormalizationFunctionField_scalar,
    curveAffineNormalizationFunctionFieldAlgEquiv_algebraMap]
  change curveCoefficientRatFuncMap k h a b hh
      (algebraMap k[X] (RatFunc k) (algebraMap k k[X] c)) = algebraMap k L₀ c
  rw [← IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
  exact (curveCoefficientRatFuncMap k h a b hh).commutes c

end CoefficientField

end

end ChenRanks
