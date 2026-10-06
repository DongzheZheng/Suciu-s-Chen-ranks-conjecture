import Mathlib
import ChenRanks.DifferentialAlgebraicDependence

/-!
# Actual restriction of function-field differentials

For a compatible tower of characteristic-zero fields `C → L → κ`,
the actual map `Ω[L/C] → Ω[κ/C]` is injective when `κ/L` is essentially
of finite type.  Formal smoothness is proved from perfectness and finite
type by mathlib, and the injectivity is obtained from the actual
Jacobi–Zariski base-change map and faithful flatness.

The map therefore preserves independence over the constant field `C`.
No injectivity detector or assumed preservation of independence is used.
The construction of a geometrically horizontal divisor and of its field
embedding `L → κ` remains outside this module.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

section FieldTower

variable (C L κ : Type*) [Field C] [CharZero C] [Field L] [Field κ]
  [Algebra C L] [Algebra C κ] [Algebra L κ] [IsScalarTower C L κ]

/-- A genuine essentially finite-type extension of characteristic-zero
fields gives an injective actual differential restriction map. -/
theorem curveRestriction_map_injective [Algebra.EssFiniteType L κ] :
    Function.Injective (KaehlerDifferential.map C C L κ) := by
  letI : CharZero L := Algebra.charZero_of_charZero C L
  rw [injective_iff_map_eq_zero]
  intro ω hω
  have ht : (1 : κ) ⊗ₜ[L] ω = 0 := by
    apply differential_baseChange_injective C L κ
    simpa only [KaehlerDifferential.mapBaseChange_tmul, one_smul, map_zero] using hω
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff L Ω[L⁄C]
    (A := κ) ω).mp ht

/-- Essential finite type of the target over the constant field implies
essential finite type over the actual intermediate field.  This is the
forward change-of-base theorem, not a converse from an ambient field. -/
theorem curveRestriction_map_injective_of_essFiniteType_over_base
    [Algebra.EssFiniteType C κ] :
    Function.Injective (KaehlerDifferential.map C C L κ) := by
  letI : Algebra.EssFiniteType L κ := Algebra.EssFiniteType.of_comp C L κ
  exact curveRestriction_map_injective C L κ

/-- The same actual map preserves independence over the constant field;
the required injectivity has been proved, rather than passed as an input. -/
theorem curveRestriction_preserves_linearIndependent
    [Algebra.EssFiniteType L κ] {ι : Type*} (η : ι → Ω[L⁄C])
    (hη : LinearIndependent C η) :
    LinearIndependent C (fun i ↦ KaehlerDifferential.map C C L κ (η i)) := by
  let f : Ω[L⁄C] →ₗ[C] Ω[κ⁄C] :=
    (KaehlerDifferential.map C C L κ).restrictScalars C
  exact hη.map' f (LinearMap.ker_eq_bot.mpr (curveRestriction_map_injective C L κ))

/-- The geometric-target finite-type version of constant-field
independence preservation. -/
theorem curveRestriction_preserves_linearIndependent_of_essFiniteType_over_base
    [Algebra.EssFiniteType C κ] {ι : Type*} (η : ι → Ω[L⁄C])
    (hη : LinearIndependent C η) :
    LinearIndependent C (fun i ↦ KaehlerDifferential.map C C L κ (η i)) := by
  letI : Algebra.EssFiniteType L κ := Algebra.EssFiniteType.of_comp C L κ
  exact curveRestriction_preserves_linearIndependent C L κ η hη

end FieldTower

section ActualResidueField

variable (C A : Type*) [CommRing C] [CommRing A] [Algebra C A]
  [IsLocalRing A] [Algebra.EssFiniteType C A]

/-- The actual residue field of an essentially finite-type local ring
inherits essential finite type by the quotient theorem.  This supplies
the target-field finiteness once the geometric local ring is available. -/
theorem curveRestriction_residueField_essFiniteType :
    Algebra.EssFiniteType C (IsLocalRing.ResidueField A) := by
  change Algebra.EssFiniteType C (A ⧸ IsLocalRing.maximalIdeal A)
  infer_instance

end ActualResidueField

end ChenRanks
