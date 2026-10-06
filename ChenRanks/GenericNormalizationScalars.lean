import ChenRanks.GenericNormalizationFunctionField
import ChenRanks.RationalGraphFunctionField

/-!
# Original field and scalar compatibility for actual normalization

The field comparison constructed from the actual generic point is
identified with the inverse of the actual normalization projection's
generic-stalk map. Consequently it preserves the actual structural
coefficient-field action. No desired comparison identity is assumed.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable (X : Scheme.{u}) [IsIntegral X]

private theorem actualDominantFieldMap_congr {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (f g : A ⟶ B) [IsDominant f] [IsDominant g]
    (h : f = g) : dominantFunctionFieldMap f = dominantFunctionFieldMap g := by
  subst g
  rfl

theorem genericFieldSpectrumFunctionFieldEquiv_algebraMap (x : X.functionField) :
    letI : Algebra X.functionField (Spec X.functionField).functionField :=
      instAlgebraCarrierFunctionFieldSpec X.functionField
    genericFieldSpectrumFunctionFieldEquiv X
      (algebraMap X.functionField (Spec X.functionField).functionField x) = x := by
  letI : Algebra X.functionField (Spec X.functionField).functionField :=
    instAlgebraCarrierFunctionFieldSpec X.functionField
  letI : IsFractionRing X.functionField (Spec X.functionField).functionField :=
    functionField_isFractionRing_of_affine X.functionField
  exact (IsLocalization.algEquiv (nonZeroDivisors X.functionField)
    (Spec X.functionField).functionField X.functionField).commutes x

theorem genericPointFunctionFieldMap_eq_algebraMap :
    letI : IsDominant (genericPointMorphism X) := genericPointMorphism_isDominant X
    letI : Algebra X.functionField (Spec X.functionField).functionField :=
      instAlgebraCarrierFunctionFieldSpec X.functionField
    (dominantFunctionFieldMap (genericPointMorphism X)).hom =
      algebraMap X.functionField (Spec X.functionField).functionField := by
  letI : IsDominant (genericPointMorphism X) := genericPointMorphism_isDominant X
  letI : Algebra X.functionField (Spec X.functionField).functionField :=
    instAlgebraCarrierFunctionFieldSpec X.functionField
  have hAlg :
      Spec.map (CommRingCat.ofHom
        (algebraMap X.functionField (Spec X.functionField).functionField)) =
        (Spec X.functionField).fromSpecStalk (genericPoint (Spec X.functionField)) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  have hm : dominantFunctionFieldMap (genericPointMorphism X) =
      CommRingCat.ofHom (algebraMap X.functionField (Spec X.functionField).functionField) := by
    apply Spec.map_injective
    apply (cancel_mono (genericPointMorphism X)).mp
    rw [dominantFunctionFieldMap_spec_comp, hAlg]
  exact congrArg CommRingCat.Hom.hom hm

theorem actualNormalizationFunctionFieldEquiv_symm_eq_projection :
    (actualNormalizationFunctionFieldEquiv X).symm.toRingHom =
      (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X)).hom := by
  letI : IsDominant (genericPointMorphism X) := genericPointMorphism_isDominant X
  letI : Algebra X.functionField (Spec X.functionField).functionField :=
    instAlgebraCarrierFunctionFieldSpec X.functionField
  ext x
  apply (actualNormalizationFunctionFieldEquiv X).injective
  change actualNormalizationFunctionFieldEquiv X
      ((actualNormalizationFunctionFieldEquiv X).symm x) =
    actualNormalizationFunctionFieldEquiv X
      ((dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X)).hom x)
  rw [RingEquiv.apply_symm_apply]
  have hc := dominantFunctionFieldMap_comp
    (actualNormalizationGenericMorphism X) (actualFiniteTypeNormalizationMap X)
  have hc' := hc.trans (actualDominantFieldMap_congr
    (actualNormalizationGenericMorphism X ≫ actualFiniteTypeNormalizationMap X)
    (genericPointMorphism X) ((genericPointMorphism X).toNormalization_fromNormalization))
  have hx := congrArg (fun f : X.functionField ⟶ (Spec X.functionField).functionField ↦ f x) hc'
  change (dominantFunctionFieldMap (actualNormalizationGenericMorphism X)).hom
      ((dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X)).hom x) =
    (dominantFunctionFieldMap (genericPointMorphism X)).hom x at hx
  change x = genericFieldSpectrumFunctionFieldEquiv X
    ((dominantFunctionFieldMap (actualNormalizationGenericMorphism X)).hom
      ((dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X)).hom x))
  rw [hx, genericPointFunctionFieldMap_eq_algebraMap,
    genericFieldSpectrumFunctionFieldEquiv_algebraMap]

variable {k : Type u} [Field k]

/-- The actual original-field scalar structure of the actual normalization. -/
abbrev actualNormalizationScalarMorphism (σ : X ⟶ Spec (.of k)) :
    actualFiniteTypeNormalization X ⟶ Spec (.of k) :=
  actualFiniteTypeNormalizationMap X ≫ σ

/-- The actual field comparison fixes the original structural coefficient field. -/
def actualNormalizationFunctionFieldAlgEquiv (σ : X ⟶ Spec (.of k)) :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
    letI : Algebra k (actualFiniteTypeNormalization X).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism X σ)
    (actualFiniteTypeNormalization X).functionField ≃ₐ[k] X.functionField := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
  letI : Algebra k (actualFiniteTypeNormalization X).functionField :=
    structureFunctionFieldAlgebra (actualNormalizationScalarMorphism X σ)
  let e : X.functionField ≃ₐ[k] (actualFiniteTypeNormalization X).functionField :=
    { (actualNormalizationFunctionFieldEquiv X).symm with
      commutes' := by
        intro c
        change (actualNormalizationFunctionFieldEquiv X).symm.toRingHom
            (structureFunctionFieldScalarHom σ c) =
          structureFunctionFieldScalarHom (actualNormalizationScalarMorphism X σ) c
        rw [actualNormalizationFunctionFieldEquiv_symm_eq_projection]
        exact congrArg (fun h : (.of k) ⟶ (actualFiniteTypeNormalization X).functionField ↦ h c)
          (structureFunctionFieldScalarHom_comp_dominantFunctionFieldMap
            (actualNormalizationScalarMorphism X σ) σ (actualFiniteTypeNormalizationMap X) rfl) }
  exact e.symm

end ChenRanks
