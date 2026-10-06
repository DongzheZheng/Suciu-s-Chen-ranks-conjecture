import ChenRanks.ActualSchemeImage
import ChenRanks.AffineFiniteNormalization
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Actual generic-point sections on original scheme charts

For the actual generic-point morphism of an integral scheme, the
preimage of each nonempty open is the entire actual field spectrum.
The resulting section-ring comparison is proved to carry the actual
pullback to the original germ. This is the coordinate interface needed
to apply finite normalization to the native normalization diagram.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original generic point's actual field-spectrum morphism. -/
abbrev genericPointMorphism : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- Every point of the actual field spectrum maps to the original generic point. -/
theorem genericPointMorphism_apply (z : Spec X.functionField) :
    genericPointMorphism X z = genericPoint X := by
  letI : Subsingleton (Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  have hz : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  rw [hz]
  exact Scheme.fromSpecStalk_closedPoint

/-- Actual dominance follows from the actual generic-point image. -/
theorem genericPointMorphism_isDominant : IsDominant (genericPointMorphism X) := by
  constructor
  apply dense_iff_closure_eq.mpr
  have hrange : Set.range (genericPointMorphism X) = {genericPoint X} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_singleton_iff.mpr (genericPointMorphism_apply X z)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨IsLocalRing.closedPoint X.functionField,
        (genericPointMorphism_apply X _).trans hx.symm⟩
  rw [hrange]
  exact genericPoint_spec X

/-- The actual preimage of each nonempty open is the whole field spectrum. -/
theorem genericPointMorphism_preimage (U : X.Opens) [Nonempty U] :
    genericPointMorphism X ⁻¹ᵁ U = ⊤ := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  ext z
  change genericPointMorphism X z ∈ U ↔ True
  rw [iff_true]
  rw [genericPointMorphism_apply]
  exact hη

/-- The actual pullback-open section ring is compared with the original
function field through the native structure sheaf and spectrum comparison. -/
def genericPointPreimageSectionIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
      (eqToIso (genericPointMorphism_preimage X U).symm).op ≪≫
    Scheme.ΓSpecIso X.functionField

/-- The constructed comparison takes actual scheme pullbacks to the
original germ, so it remembers the original chart embedding. -/
theorem genericPointPreimageSectionIso_pullback (U : X.Opens) [Nonempty U] :
    (genericPointMorphism X).app U ≫ (genericPointPreimageSectionIso X U).hom =
      X.presheaf.germ U (genericPoint X)
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
          (by simpa using ‹Nonempty U›)) := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  rw [Scheme.fromSpecStalk_app (X := X) (U := U) hη]
  dsimp [genericPointPreimageSectionIso]
  have hmaps :
      (Spec X.functionField).presheaf.map
          (homOfLE (show genericPointMorphism X ⁻¹ᵁ U ≤ ⊤ from fun _ _ ↦ trivial)).op ≫
        (Spec X.functionField).presheaf.map
          (eqToHom (genericPointMorphism_preimage X U).symm).op =
        𝟙 Γ(Spec X.functionField, ⊤) := by
    rw [← CategoryTheory.Functor.map_comp]
    have heq :
        (homOfLE (show genericPointMorphism X ⁻¹ᵁ U ≤ ⊤ from fun _ _ ↦ trivial)).op ≫
          (eqToHom (genericPointMorphism_preimage X U).symm).op =
          𝟙 (op (⊤ : (Spec X.functionField).Opens)) := Subsingleton.elim _ _
    rw [heq, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (Scheme.ΓSpecIso X.functionField).hom, hmaps]
  simp

end ChenRanks
