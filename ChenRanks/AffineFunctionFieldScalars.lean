import ChenRanks.CurveAffineRationalMap
import ChenRanks.StructureFunctionFieldTower

/-!
# Original affine structure scalars in actual function fields

For an actual scalar ring map k → B, the actual structure map Spec B →
Spec k induces the actual scalar germ k → K(Spec B).  Spec faithfulness
identifies it with the actual coordinate scalar followed by the actual
generic coordinate germ.  The actual fraction comparison therefore
preserves the constructed original scalar action without a compatibility
premise.  This is used for the actual projective standard chart.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable (k B : Type u) [Field k] [CommRing B] [IsDomain B]

/-- The actual structure scalar germ on an actual affine spectrum. -/
theorem affineFunctionFieldScalarHom_eq_coordinates (ρ : k →+* B) :
    structureFunctionFieldScalarHom (Spec.map (CommRingCat.ofHom ρ)) =
      CommRingCat.ofHom ((algebraMap B (Spec (.of B)).functionField).comp ρ) := by
  apply Spec.map_injective
  rw [structureFunctionFieldScalarHom_spec]
  have hB : Spec.map (CommRingCat.ofHom (algebraMap B (Spec (.of B)).functionField)) =
      (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  rw [← hB, ← Spec.map_comp]
  rfl

/-- The original action on an actual fraction field is constructed from
its actual coordinate-ring map and its actual original scalar map. -/
abbrev affineFractionBaseAlgebra (F : Type u) [Field F] [Algebra B F]
    (ρ : k →+* B) : Algebra k F :=
  ((algebraMap B F).comp ρ).toAlgebra

variable (F : Type u) [Field F] [Algebra B F] [IsFractionRing B F]

/-- The genuine affine fraction comparison preserves the actual
structure scalars, with both actions constructed from the same map ρ. -/
def affineFunctionFieldBaseAlgEquiv (ρ : k →+* B) :
    letI : Algebra k (Spec (.of B)).functionField :=
      structureFunctionFieldAlgebra (Spec.map (CommRingCat.ofHom ρ))
    letI : Algebra k F := affineFractionBaseAlgebra k B F ρ
    (Spec (.of B)).functionField ≃ₐ[k] F := by
  letI : Algebra k (Spec (.of B)).functionField :=
    structureFunctionFieldAlgebra (Spec.map (CommRingCat.ofHom ρ))
  letI : Algebra k F := affineFractionBaseAlgebra k B F ρ
  refine { (affineCoordinateFunctionFieldEquiv B F).toRingEquiv with commutes' := ?_ }
  intro c
  change affineCoordinateFunctionFieldEquiv B F
      (structureFunctionFieldScalarHom (Spec.map (CommRingCat.ofHom ρ)) c) =
    algebraMap B F (ρ c)
  rw [affineFunctionFieldScalarHom_eq_coordinates]
  exact (affineCoordinateFunctionFieldEquiv B F).commutes (ρ c)

end

end ChenRanks
