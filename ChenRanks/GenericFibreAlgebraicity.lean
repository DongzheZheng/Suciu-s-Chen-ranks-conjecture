import ChenRanks.GenericFibreFunctionField

/-!
# Actual scalars and regular functions on the reduced generic fibre

The function-field comparison is induced by the actual generic-stalk map
of the actual projection.  This file proves that this comparison respects
the actual scalar homomorphism supplied by the actual generic pullback
square.  Consequently algebraicity may be transported over the original
base function field, rather than across an arbitrary field isomorphism.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

variable {k : Type u} [Field k] {Z : Scheme.{u}} [IsIntegral Z]

/-- Actual scalar values in the actual function field, as a categorical
ring homomorphism obtained from the structure morphism and generic germ. -/
def structureFunctionFieldScalarHom (σ : Z ⟶ Spec (.of k)) :
    (.of k) ⟶ Z.functionField :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ σ.appTop ≫ topFunctionFieldGerm Z

/-- The scalar homomorphism is geometrically the actual structure
morphism restricted to the actual generic-point spectrum. -/
@[reassoc]
theorem structureFunctionFieldScalarHom_spec (σ : Z ⟶ Spec (.of k)) :
    Spec.map (structureFunctionFieldScalarHom σ) =
      Z.fromSpecStalk (genericPoint Z) ≫ σ := by
  rw [structureFunctionFieldScalarHom, Spec.map_comp, Spec.map_comp]
  change Spec.map (Z.presheaf.germ ⊤ (genericPoint Z) (by trivial)) ≫
      Spec.map σ.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv = _
  rw [← Scheme.fromSpecStalk_toSpecΓ]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc σ]
  simp

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic-fibre function-field comparison commutes with
the actual base function-field maps, by the actual scheme pullback square. -/
theorem reducedGenericFibre_scalar_compatibility (f : X ⟶ Y) [IsDominant f] :
    dominantFunctionFieldMap f ≫ reducedGenericFibreFunctionFieldMap f =
      structureFunctionFieldScalarHom (reducedGenericFibreScalarMorphism f) := by
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  calc
    Spec.map (dominantFunctionFieldMap f ≫ reducedGenericFibreFunctionFieldMap f) ≫
        Y.fromSpecStalk (genericPoint Y) =
        Spec.map (reducedGenericFibreFunctionFieldMap f) ≫
          (Spec.map (dominantFunctionFieldMap f) ≫
            Y.fromSpecStalk (genericPoint Y)) := by
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (reducedGenericFibreFunctionFieldMap f) ≫
          (X.fromSpecStalk (genericPoint X) ≫ f) := by
      rw [dominantFunctionFieldMap_spec_comp f]
    _ = ((reducedGenericFibre f).fromSpecStalk (genericPoint (reducedGenericFibre f)) ≫
          reducedGenericFibreProjection f) ≫ f := by
      rw [← Category.assoc, dominantFunctionFieldMap_spec_comp]
    _ = (reducedGenericFibre f).fromSpecStalk (genericPoint (reducedGenericFibre f)) ≫
          (reducedGenericFibreScalarMorphism f ≫
            Y.fromSpecStalk (genericPoint Y)) := by
      rw [Category.assoc, reducedGenericFibre_square]
    _ = Spec.map (structureFunctionFieldScalarHom (reducedGenericFibreScalarMorphism f)) ≫
          Y.fromSpecStalk (genericPoint Y) := by
      rw [structureFunctionFieldScalarHom_spec, Category.assoc]

/-- The actual projection-induced comparison is an equivalence of
algebras over the original base function field.  Both scalar actions are
constructed from actual morphisms; compatibility is a proved conclusion. -/
def reducedGenericFibreFunctionFieldAlgEquiv (f : X ⟶ Y) [IsDominant f] :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : Algebra Y.functionField (reducedGenericFibre f).functionField :=
      structureFunctionFieldAlgebra (reducedGenericFibreScalarMorphism f)
    X.functionField ≃ₐ[Y.functionField] (reducedGenericFibre f).functionField := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : Algebra Y.functionField (reducedGenericFibre f).functionField :=
    structureFunctionFieldAlgebra (reducedGenericFibreScalarMorphism f)
  refine { toRingEquiv := reducedGenericFibreFunctionFieldEquiv f, commutes' := ?_ }
  intro a
  change reducedGenericFibreFunctionFieldMap f (dominantFunctionFieldMap f a) =
    structureFunctionFieldScalarHom (reducedGenericFibreScalarMorphism f) a
  exact congrArg (fun h : Y.functionField ⟶ (reducedGenericFibre f).functionField => h a)
    (reducedGenericFibre_scalar_compatibility f)

end

end ChenRanks
