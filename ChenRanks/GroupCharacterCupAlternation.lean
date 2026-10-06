import ChenRanks.GroupCharacterCup
import ChenRanks.ExteriorSeparationLinearEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-! Native original group-character cups are alternating over a
characteristic-zero field. The native bar primitives are explicitly
constructed. The antisymmetric bar cochain represents twice the genuine
exterior cup, with its scalar and sign checked in the original H2.
-/

noncomputable section
namespace ChenRanks

variable (k G : Type) [Field k] [Group G]

/-- A verified native bar primitive kills its actual original H2 class. -/
theorem groupBarCocycle_class_zero_of_primitive
    (c : groupCohomology.cocycles₂ (groupTrivialCoefficients k G))
    (f : G → k) (hf : ∀ g h, f h - f (g * h) + f g = c (g, h)) :
    groupCohomology.H2π (groupTrivialCoefficients k G) c = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨f, ?_⟩
  funext gh
  simp only [groupCohomology.d₁₂_hom_apply]
  exact hf gh.1 gh.2

/-- The actual symmetric character cup has an actual bar primitive. -/
theorem groupCharacterCup_add_swap_eq_zero (χ ψ : Additive G →+ k) :
    groupCharacterCup k G χ ψ + groupCharacterCup k G ψ χ = 0 := by
  change (groupCohomology.H2π (groupTrivialCoefficients k G)).hom
      (groupCharacterCupCocycle k G χ ψ) +
    (groupCohomology.H2π (groupTrivialCoefficients k G)).hom
      (groupCharacterCupCocycle k G ψ χ) = 0
  rw [← map_add]
  apply groupBarCocycle_class_zero_of_primitive k G _
    (fun g => -χ (Additive.ofMul g) * ψ (Additive.ofMul g))
  intro g h
  change -χ (Additive.ofMul h) * ψ (Additive.ofMul h) -
    (-χ (Additive.ofMul (g * h)) * ψ (Additive.ofMul (g * h))) +
    -χ (Additive.ofMul g) * ψ (Additive.ofMul g) =
      χ (Additive.ofMul g) * ψ (Additive.ofMul h) +
        ψ (Additive.ofMul g) * χ (Additive.ofMul h)
  rw [ofMul_mul, map_add, map_add]
  ring

variable [CharZero k]

/-- The diagonal cup is killed by its actual quadratic bar primitive. -/
theorem groupCharacterCup_self_eq_zero (χ : Additive G →+ k) :
    groupCharacterCup k G χ χ = 0 := by
  apply (groupCharacterCup_eq_zero_iff k G χ χ).mpr
  refine ⟨fun g => -(2 : k)⁻¹ * χ (Additive.ofMul g) ^ 2, ?_⟩
  intro g h
  dsimp only
  simp only [ofMul_mul, map_add]
  field_simp
  ring

@[simp] theorem groupCharacterCupBilinear_apply (χ ψ : Additive G →+ k) :
    groupCharacterCupBilinear k G χ ψ = groupCharacterCup k G χ ψ := rfl

/-- The actual alternating character cup, independent of any space model. -/
def groupCharacterAlternatingCup :
    (Additive G →+ k) [⋀^Fin 2]→ₗ[k] groupCohomology.H2 (groupTrivialCoefficients k G) where
  toFun a := groupCharacterCupBilinear k G (a 0) (a 1)
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change groupCharacterCup k G (a 0) (a 1) = 0
      rw [h]
      exact groupCharacterCup_self_eq_zero k G (a 1)
    · change a 1 = a 0 at h
      change groupCharacterCup k G (a 0) (a 1) = 0
      rw [h]
      exact groupCharacterCup_self_eq_zero k G (a 0)
    · exact (hij rfl).elim

/-- Genuine exterior-square cup into the original native group H2. -/
def groupCharacterQuadraticCup :
    (⋀[k]^2 (Additive G →+ k)) →ₗ[k] groupCohomology.H2 (groupTrivialCoefficients k G) :=
  exteriorPower.alternatingMapLinearEquiv (groupCharacterAlternatingCup k G)

theorem groupCharacterQuadraticCup_exteriorWedge (χ ψ : Additive G →+ k) :
    groupCharacterQuadraticCup k G (exteriorWedge (k := k) χ ψ) =
      groupCharacterCup k G χ ψ := by
  simp [groupCharacterQuadraticCup, exteriorWedge, groupCharacterAlternatingCup]

/-- Actual antisymmetric bar evaluation gives exactly twice the genuine
exterior cup class. This coefficient is not silently discarded. -/
theorem groupCharacterSkewCocycle_class_eq_two_cup (χ ψ : Additive G →+ k) :
    groupCohomology.H2π (groupTrivialCoefficients k G)
      (groupCharacterCupCocycle k G χ ψ - groupCharacterCupCocycle k G ψ χ) =
      (2 : k) • groupCharacterQuadraticCup k G (exteriorWedge (k := k) χ ψ) := by
  rw [groupCharacterQuadraticCup_exteriorWedge]
  change (groupCohomology.H2π (groupTrivialCoefficients k G)).hom
      (groupCharacterCupCocycle k G χ ψ - groupCharacterCupCocycle k G ψ χ) = _
  rw [map_sub]
  have h := groupCharacterCup_add_swap_eq_zero k G χ ψ
  change groupCharacterCup k G χ ψ - groupCharacterCup k G ψ χ = _
  rw [two_smul]
  have hneg : groupCharacterCup k G ψ χ = -groupCharacterCup k G χ ψ :=
    eq_neg_of_add_eq_zero_right h
  rw [hneg, sub_neg_eq_add]

end ChenRanks
