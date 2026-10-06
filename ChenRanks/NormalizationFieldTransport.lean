import ChenRanks.NormalizedProjectiveCoefficientFieldObjects

/-!
# Native normalization and structural field transport

The actual normalization comparison, refined to preserve the original
structural field action, cancels the actual normalization projection in
an arbitrary dominant composite.  This is an equality of the actual
ring homomorphisms, proved from native function-field functoriality; no
projection compatibility is assumed.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  (X : Scheme.{u}) [IsIntegral X] {C : Scheme.{u}} [IsIntegral C]

/-- The scalar-preserving normalization comparison has the already
constructed native ring comparison as its underlying ring homomorphism. -/
theorem actualNormalizationFunctionFieldAlgEquiv_toRingHom
    (σ : X ⟶ Spec (.of k)) :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
    letI : Algebra k (actualFiniteTypeNormalization X).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism X σ)
    (actualNormalizationFunctionFieldAlgEquiv X σ).toRingHom =
      (actualNormalizationFunctionFieldEquiv X).toRingHom := by
  rfl

/-- Composing the actual structural normalization comparison with an
actual original-field comparison cancels the actual normalization
projection inside every dominant morphism to an integral scheme. -/
theorem actualNormalizationAlgEquiv_transport_comp
    (σ : X ⟶ Spec (.of k)) (f : X ⟶ C) [IsDominant f] :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
    letI : Algebra k (actualFiniteTypeNormalization X).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism X σ)
    ∀ e : X.functionField ≃ₐ[k] F,
      ((actualNormalizationFunctionFieldAlgEquiv X σ).trans e).toRingHom.comp
          (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X ≫ f)).hom =
        e.toRingHom.comp (dominantFunctionFieldMap f).hom := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σ
  letI : Algebra k (actualFiniteTypeNormalization X).functionField :=
    structureFunctionFieldAlgebra (actualNormalizationScalarMorphism X σ)
  intro e
  change e.toRingHom.comp
      ((actualNormalizationFunctionFieldEquiv X).toRingHom.comp
        (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap X ≫ f)).hom) =
    e.toRingHom.comp (dominantFunctionFieldMap f).hom
  exact congrArg (fun g : C.functionField →+* X.functionField => e.toRingHom.comp g)
    (actualNormalizationFunctionFieldEquiv_comp_morphism X f)

end ChenRanks
