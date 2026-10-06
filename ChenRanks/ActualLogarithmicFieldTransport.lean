import ChenRanks.DifferentialFieldTransport
import ChenRanks.ValuationKernelDifferentials
import ChenRanks.ArrangementCurveField

/-!
# The actual logarithmic generators under an actual field comparison

The nonzero original rational functions are transported as actual units.
The already proved differential comparison carries their actual logarithmic
forms. Linearity then identifies the whole original logarithmic realization
with the actual logarithmic combination on the model and identifies their
actual ranges. Neither a range equality nor a transported maximality is
supplied as a premise.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable {F G : Type*} [Field F] [Field G] [Algebra ℂ F] [Algebra ℂ G]
  {j : Type*} [Fintype j]

/-- The actual mapped units give exactly the transported logarithmic
combination, coefficient by coefficient. -/
theorem relativeLogCombination_mapUnits_eq
    (e : F ≃ₐ[ℂ] G) (u : j → Fˣ) (c : j → ℂ) :
    relativeLogCombination (L := ℂ)
        (fun a ↦ Units.map e.toRingHom.toMonoidHom (u a)) c =
      differentialFieldLinearEquiv e (relativeLogCombination (L := ℂ) u c) := by
  simp only [relativeLogCombination, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul, differentialFieldLinearEquiv_logarithmic]

/-- The model's actual logarithmic map is the actual differential
comparison composed with the original logarithmic map. -/
theorem relativeLogCombination_mapUnits_eq_comp
    (e : F ≃ₐ[ℂ] G) (u : j → Fˣ) :
    relativeLogCombination (L := ℂ)
        (fun a ↦ Units.map e.toRingHom.toMonoidHom (u a)) =
      (differentialFieldLinearEquiv e).toLinearMap.comp
        (relativeLogCombination (L := ℂ) u) := by
  ext c
  exact relativeLogCombination_mapUnits_eq e u c

/-- The entire model logarithmic space is the actual image of the
original logarithmic space. This is a conclusion from actual generators. -/
theorem relativeLogCombination_mapUnits_range
    (e : F ≃ₐ[ℂ] G) (u : j → Fˣ) :
    LinearMap.range (relativeLogCombination (L := ℂ)
        (fun a ↦ Units.map e.toRingHom.toMonoidHom (u a))) =
      (LinearMap.range (relativeLogCombination (L := ℂ) u)).map
        (differentialFieldLinearEquiv e).toLinearMap := by
  ext ω
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨relativeLogCombination (L := ℂ) u c, ⟨c, rfl⟩,
      (relativeLogCombination_mapUnits_eq e u c).symm⟩
  · rintro ⟨η, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, relativeLogCombination_mapUnits_eq e u c⟩

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual equation units of the arrangement, transported to an
actual comparison field, span exactly the transported original log space. -/
theorem equationUnits_map_logarithmic_range
    (e : RationalFunctionField (d := d) ≃ₐ[ℂ] G) :
    LinearMap.range (relativeLogCombination (L := ℂ)
        (fun H ↦ Units.map e.toRingHom.toMonoidHom (A.equationUnit H))) =
      A.logarithmicForms.map (differentialFieldLinearEquiv e).toLinearMap := by
  have hreal : relativeLogCombination (L := ℂ) A.equationUnit =
      A.logarithmicRealization := by
    ext c
    rfl
  rw [relativeLogCombination_mapUnits_range, hreal]
  rfl

end AffineArrangement

end ChenRanks
