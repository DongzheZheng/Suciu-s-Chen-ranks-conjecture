import ChenRanks.GenericPointFiniteNormalization
import ChenRanks.AffineGenericFieldMap

/-!
# The original function field of the actual native normalization

The normalization's field comparison is constructed from its actual
generic-point factorization. The actual generic map is a preimmersion:
its source is a singleton field spectrum and surjectivity on stalks
follows from the original generic-point morphism's actual factorization.
Thus no birational equivalence or function-field isomorphism is an input.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory Topology

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual generic-point factor through the native normalization. -/
abbrev actualNormalizationGenericMorphism :
    Spec X.functionField ⟶ actualFiniteTypeNormalization X :=
  (genericPointMorphism X).toNormalization

instance actualNormalizationGenericMorphism_isPreimmersion :
    IsPreimmersion (actualNormalizationGenericMorphism X) := by
  letI : Subsingleton (Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  have hcomp : actualNormalizationGenericMorphism X ≫ actualFiniteTypeNormalizationMap X =
      genericPointMorphism X :=
    (genericPointMorphism X).toNormalization_fromNormalization
  haveI : IsPreimmersion
      (actualNormalizationGenericMorphism X ≫ actualFiniteTypeNormalizationMap X) := by
    rw [hcomp]
    infer_instance
  refine { isEmbedding := IsEmbedding.of_subsingleton _, stalkMap_surjective := ?_ }
  intro x
  have h := (actualNormalizationGenericMorphism X ≫
    actualFiniteTypeNormalizationMap X).stalkMap_surjective x
  rw [Scheme.Hom.stalkMap_comp] at h
  exact Function.Surjective.of_comp h

instance actualNormalizationGenericMorphism_isDominant :
    IsDominant (actualNormalizationGenericMorphism X) := by
  infer_instance

instance actualFiniteTypeNormalizationMap_isDominant :
    IsDominant (actualFiniteTypeNormalizationMap X) := by
  haveI : IsDominant (genericPointMorphism X) := genericPointMorphism_isDominant X
  haveI : IsDominant
      (actualNormalizationGenericMorphism X ≫ actualFiniteTypeNormalizationMap X) := by
    rw [(genericPointMorphism X).toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp (actualNormalizationGenericMorphism X)
    (actualFiniteTypeNormalizationMap X)

/-- The actual field-spectrum generic stalk is its original field. -/
def genericFieldSpectrumFunctionFieldEquiv :
    (Spec X.functionField).functionField ≃+* X.functionField := by
  letI : Algebra X.functionField (Spec X.functionField).functionField :=
    instAlgebraCarrierFunctionFieldSpec X.functionField
  letI : IsFractionRing X.functionField (Spec X.functionField).functionField :=
    functionField_isFractionRing_of_affine X.functionField
  exact (IsLocalization.algEquiv (nonZeroDivisors X.functionField)
    (Spec X.functionField).functionField X.functionField).toRingEquiv

/-- The actual native normalization preserves the original scheme
function field through its actual generic-point morphism. -/
def actualNormalizationFunctionFieldEquiv :
    (actualFiniteTypeNormalization X).functionField ≃+* X.functionField :=
  (dominantPreimmersionFunctionFieldEquiv (actualNormalizationGenericMorphism X)).trans
    (genericFieldSpectrumFunctionFieldEquiv X)

end ChenRanks
