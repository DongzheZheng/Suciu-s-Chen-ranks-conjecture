import ChenRanks.ProperConstancy
import ChenRanks.SchemeRegularExtension

/-!
# Actual restriction of regular functions to proper fibre components

A fibre component does not dominate the ambient variety.  Accordingly,
there is no pullback homomorphism on the entire ambient function field.
This file first uses an actual section on an actual open subscheme, then
restricts it along an actual scheme morphism by `appLE`.  The result is an
actual global regular function on the component, to which the actual
proper integral constancy theorem applies.

An actual inverse section proves that the ambient section is a unit;
restriction preserves units and thus makes the resulting fibre constant
nonzero.  The source fibre/component and its morphism are structural
inputs here, not assertions of function constancy.  Their construction
from the manuscript's curve morphism remains a separate geometric step.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

variable {X Z : Scheme.{u}}

private theorem point_mem_open_of_factor (V : X.Opens) (g : Z ⟶ V.toScheme) (z : Z) :
    (g ≫ V.ι) z ∈ V := by
  rw [Scheme.Hom.comp_apply]
  exact (g z).property

private theorem top_le_preimage_of_open_factor (V : X.Opens) (g : Z ⟶ V.toScheme) :
    (⊤ : Z.Opens) ≤ (g ≫ V.ι) ⁻¹ᵁ V := by
  intro z _
  exact point_mem_open_of_factor V g z

/-- The actual restriction from sections on the ambient open to actual
global sections on a scheme which factors through that open. -/
def regularSectionRestriction (V : X.Opens) (g : Z ⟶ V.toScheme) :
    Γ(X, V) →+* Γ(Z, ⊤) :=
  ((g ≫ V.ι).appLE V ⊤ (top_le_preimage_of_open_factor V g)).hom

/-- Actual inverse rational germs give an actual unit in the actual open
section ring.  The section ring is not identified with the function field. -/
theorem section_isUnit_of_inverse_generic_germs [IsIntegral X]
    (V : X.Opens) [Nonempty V] (x : X.functionField) (hx : x ≠ 0)
    (s t : Γ(X, V)) (hs : X.germToFunctionField V s = x)
    (ht : X.germToFunctionField V t = x⁻¹) : IsUnit s := by
  have hmul : s * t = 1 := by
    apply X.germToFunctionField_injective V
    change (X.germToFunctionField V).hom (s * t) = (X.germToFunctionField V).hom 1
    rw [map_mul, hs, ht, map_one]
    exact mul_inv_cancel₀ hx
  exact isUnit_iff_exists_inv.mpr ⟨t, hmul⟩

/-- The actual scheme restriction preserves the unit established by the
actual inverse section. -/
theorem regularSectionRestriction_isUnit
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) (hs : IsUnit s) :
    IsUnit (regularSectionRestriction V g s) :=
  hs.map (regularSectionRestriction V g)

/-- Restriction and the actual stalk map give the same actual germ.
This concerns the section which has already been proved regular, not a
putative homomorphism on the entire ambient function field. -/
theorem regularSectionRestriction_germ
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) (z : Z) :
    (g ≫ V.ι).stalkMap z
        (X.presheaf.germ V ((g ≫ V.ι) z) (point_mem_open_of_factor V g z) s) =
      Z.presheaf.germ ⊤ z (by trivial) (regularSectionRestriction V g s) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact (Z.presheaf.germ_res_apply
    (homOfLE (top_le_preimage_of_open_factor V g)) z (by trivial)
      ((g ≫ V.ι).app V s)).symm

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Restricting the actual ambient regular section to an actual proper
integral component gives an actual scalar in the component's section ring. -/
theorem regularSectionRestriction_constant
    (σ : Z ⟶ Spec (.of k)) [IsIntegral Z] [UniversallyClosed σ]
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    ∃ c : k, globalScalarMap σ c = regularSectionRestriction V g s :=
  global_regular_function_constant σ (regularSectionRestriction V g s)

/-- If the ambient section has the actual inverse constructed in the
vertical-function argument, its fibre constant is nonzero. -/
theorem regularSectionRestriction_constant_nonzero
    (σ : Z ⟶ Spec (.of k)) [IsIntegral Z] [UniversallyClosed σ]
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) (hs : IsUnit s) :
    ∃ c : k, c ≠ 0 ∧ globalScalarMap σ c = regularSectionRestriction V g s := by
  obtain ⟨c, hc⟩ := regularSectionRestriction_constant σ V g s
  refine ⟨c, ?_, hc⟩
  intro hc0
  have hzero : regularSectionRestriction V g s = 0 := by rw [← hc, hc0, map_zero]
  exact (regularSectionRestriction_isUnit V g s hs).ne_zero hzero

/-- One actual fibre scalar describes all actual restricted stalk germs
on the proper integral component. -/
theorem regularSectionRestriction_germs_constant
    (σ : Z ⟶ Spec (.of k)) [IsIntegral Z] [UniversallyClosed σ]
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    ∃ c : k, ∀ z : Z,
      (g ≫ V.ι).stalkMap z
          (X.presheaf.germ V ((g ≫ V.ι) z) (point_mem_open_of_factor V g z) s) =
        Z.presheaf.germ ⊤ z (by trivial) (globalScalarMap σ c) := by
  obtain ⟨c, hc⟩ := regularSectionRestriction_constant σ V g s
  refine ⟨c, ?_⟩
  intro z
  rw [regularSectionRestriction_germ V g s z, ← hc]

/-- The proper component's actual global differential of the actual
restriction vanishes over its actual scalar algebra.  This is not yet
the relative differential in the ambient variety's function field. -/
theorem regularSectionRestriction_globalDifferential_eq_zero
    (σ : Z ⟶ Spec (.of k)) [IsIntegral Z] [UniversallyClosed σ]
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    letI : Algebra k Γ(Z, ⊤) := (globalScalarMap σ).toAlgebra
    KaehlerDifferential.D k Γ(Z, ⊤) (regularSectionRestriction V g s) = 0 :=
  global_regular_differential_eq_zero σ (regularSectionRestriction V g s)

/-- The scalar action on the actual fibre stalk is obtained by composing
the actual structure-map scalar homomorphism with the actual top germ. -/
def fibreStalkScalarMap (σ : Z ⟶ Spec (.of k)) (z : Z) :
    k →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z (by trivial)).hom.comp (globalScalarMap σ)

/-- The restricted actual section has zero differential in every actual
fibre stalk.  This statement does not identify the fibre-stalk differential
with the ambient function-field relative differential. -/
theorem regularSectionRestriction_stalkDifferential_eq_zero
    (σ : Z ⟶ Spec (.of k)) [IsIntegral Z] [UniversallyClosed σ]
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) (z : Z) :
    letI : Algebra k (Z.presheaf.stalk z) := (fibreStalkScalarMap σ z).toAlgebra
    KaehlerDifferential.D k (Z.presheaf.stalk z)
      (Z.presheaf.germ ⊤ z (by trivial) (regularSectionRestriction V g s)) = 0 := by
  letI : Algebra k (Z.presheaf.stalk z) := (fibreStalkScalarMap σ z).toAlgebra
  obtain ⟨c, hc⟩ := regularSectionRestriction_constant σ V g s
  rw [← hc]
  change KaehlerDifferential.D k (Z.presheaf.stalk z)
    (algebraMap k (Z.presheaf.stalk z) c) = 0
  exact (KaehlerDifferential.D k (Z.presheaf.stalk z)).map_algebraMap c

/-- The actual pullback of the ambient regular germ has zero differential
in the actual fibre stalk, with its actual scalar algebra. -/
theorem regularSectionRestriction_pullbackGermDifferential_eq_zero
    (σ : Z ⟶ Spec (.of k)) [IsIntegral Z] [UniversallyClosed σ]
    (V : X.Opens) (g : Z ⟶ V.toScheme) (s : Γ(X, V)) (z : Z) :
    letI : Algebra k (Z.presheaf.stalk z) := (fibreStalkScalarMap σ z).toAlgebra
    KaehlerDifferential.D k (Z.presheaf.stalk z)
      ((g ≫ V.ι).stalkMap z
        (X.presheaf.germ V ((g ≫ V.ι) z) (point_mem_open_of_factor V g z) s)) = 0 := by
  letI : Algebra k (Z.presheaf.stalk z) := (fibreStalkScalarMap σ z).toAlgebra
  rw [regularSectionRestriction_germ V g s z]
  exact regularSectionRestriction_stalkDifferential_eq_zero σ V g s z

end

end ChenRanks
