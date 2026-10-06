import ChenRanks.HorizontalLocalDifferentials

/-!
# Actual smooth structural morphisms and their actual local algebras

The base-field algebra is exactly the scalar map constructed from the
actual structural morphism.  Its finite-type and formal-smoothness
properties are proved from the corresponding actual scheme properties,
rather than introduced as assumptions on the differential maps.

This module does not construct a resolved smooth model.  In particular,
formal smoothness is not inferred solely from being a discrete valuation
ring.  The hypothesis `Smooth σ` is the actual geometric property of the
specified structural morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

universe u

section BaseFieldStalk

variable {k : Type u} [Field k]

/-- On the actual spectrum of the base field, the constructed scalar
map is the canonical actual structure-sheaf map to the stalk. -/
theorem structureSpecStalkScalarHom_eq (p : Spec (.of k)) :
    structureStalkScalarHom (𝟙 (Spec (.of k))) p =
      StructureSheaf.toStalk k p := by
  simp [structureStalkScalarHom, StructureSheaf.toStalk, Scheme.ΓSpecIso_inv]
  rfl

/-- Localizing a field at an actual prime adds no new elements.  This
proves bijectivity of the actual base-field stalk scalar map. -/
theorem structureSpecStalkScalarHom_bijective (p : Spec (.of k)) :
    Function.Bijective (structureStalkScalarHom (𝟙 (Spec (.of k))) p) := by
  rw [structureSpecStalkScalarHom_eq]
  letI : Algebra k ((Spec (.of k)).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra (R := k) p
  letI : IsLocalization p.asIdeal.primeCompl ((Spec (.of k)).presheaf.stalk p) :=
    StructureSheaf.IsLocalization.to_stalk k p
  change Function.Bijective
    (algebraMap k ((Spec (.of k)).presheaf.stalk p))
  exact Field.localization_map_bijective (M := p.asIdeal.primeCompl) (by simp)

end BaseFieldStalk

section ActualLocalStructures

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual scalar map to the local ring factors through the actual
stalk map of the actual structural morphism. -/
theorem structureStalkScalarHom_factor (σ : X ⟶ Spec (.of k)) (x : X) :
    structureStalkScalarHom (𝟙 (Spec (.of k))) (σ x) ≫ σ.stalkMap x =
      structureStalkScalarHom σ x := by
  apply Spec.map_injective
  rw [Spec.map_comp, structureStalkScalarHom_spec]
  simp only [Category.comp_id]
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk, structureStalkScalarHom_spec]

/-- An actual locally finite-type structural morphism gives the actual
local scalar ring homomorphism essential finite type. -/
theorem structureStalkScalarHom_essFiniteType
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] (x : X) :
    (structureStalkScalarHom σ x).hom.EssFiniteType := by
  have hb : (structureStalkScalarHom (𝟙 (Spec (.of k))) (σ x)).hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (structureSpecStalkScalarHom_bijective (σ x)).2).essFiniteType
  have hs := LocallyOfFiniteType.stalkMap σ x
  have hc := hb.comp hs
  rw [← CommRingCat.hom_comp, structureStalkScalarHom_factor] at hc
  exact hc

/-- The actual local algebra inherits essential finite type with its
precise structural scalar map. -/
theorem structureStalkAlgebra_essFiniteType
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  exact structureStalkScalarHom_essFiniteType σ x

/-- At every point of an actual smooth structural morphism, its actual
stalk map is formally smooth. -/
theorem smoothStructure_stalkMap_formallySmooth
    (σ : X ⟶ Spec (.of k)) [Smooth σ] (x : X) :
    (σ.stalkMap x).hom.FormallySmooth := by
  have hx : x ∈ σ.smoothLocus := by
    rw [σ.smoothLocus_eq_top]
    trivial
  exact (Scheme.Hom.mem_smoothLocus).mp hx

/-- Actual geometric smoothness, together with the actual base-field
stalk isomorphism, proves formal smoothness of the actual scalar map. -/
theorem structureStalkScalarHom_formallySmooth
    (σ : X ⟶ Spec (.of k)) [Smooth σ] (x : X) :
    (structureStalkScalarHom σ x).hom.FormallySmooth := by
  have hb := RingHom.FormallySmooth.of_bijective
    (structureSpecStalkScalarHom_bijective (σ x))
  have hc := hb.comp (smoothStructure_stalkMap_formallySmooth σ x)
  rw [← CommRingCat.hom_comp, structureStalkScalarHom_factor] at hc
  exact hc

/-- The exact actual local algebra needed by the constructed residue
is formally smooth, as a consequence of the actual scheme morphism. -/
theorem structureStalkAlgebra_formallySmooth
    (σ : X ⟶ Spec (.of k)) [Smooth σ] (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
    Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  exact (structureStalkScalarHom_formallySmooth σ x).toAlgebra

/-- The actual residue field at the same actual point is essentially
of finite type over the same actual base-field scalar map. -/
theorem structureStalkResidueField_essFiniteType
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
    Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  letI : Algebra k (X.presheaf.stalk x) := structureStalkAlgebra σ x
  letI : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    structureStalkAlgebra_essFiniteType σ x
  exact curveRestriction_residueField_essFiniteType k (X.presheaf.stalk x)

end ActualLocalStructures

end ChenRanks
