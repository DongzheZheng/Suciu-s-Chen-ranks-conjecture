import ChenRanks.GroupCharacterCupAlternation

/-! The actual antisymmetric bar cochains descend to the actual exterior
square of genuine group characters. Native H2 projection sends the whole
exterior map to twice the genuine exterior cup, not just on a basis.
-/

noncomputable section
namespace ChenRanks
variable (k G : Type) [Field k] [Group G] [CharZero k]

private instance nativeSkewCocyclesAddCommGroup :
    AddCommGroup (groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) :=
  Submodule.addCommGroup (groupCohomology.cocycles₂ (groupTrivialCoefficients k G))

private instance nativeSkewCocyclesModule :
    Module k (groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) :=
  Submodule.module (groupCohomology.cocycles₂ (groupTrivialCoefficients k G))

def groupCharacterSkewCocycleBilinear :
    (Additive G →+ k) →ₗ[k] (Additive G →+ k) →ₗ[k]
      groupCohomology.cocycles₂ (groupTrivialCoefficients k G) :=
  groupCharacterCupCocycleBilinear k G - (groupCharacterCupCocycleBilinear k G).flip

@[simp] theorem groupCharacterSkewCocycleBilinear_apply
    (χ ψ : Additive G →+ k) :
    groupCharacterSkewCocycleBilinear k G χ ψ =
      groupCharacterCupCocycle k G χ ψ - groupCharacterCupCocycle k G ψ χ := rfl

def groupCharacterSkewAlternatingCocycle :
    (Additive G →+ k) [⋀^Fin 2]→ₗ[k]
      groupCohomology.cocycles₂ (groupTrivialCoefficients k G) where
  toFun a := groupCharacterSkewCocycleBilinear k G (a 0) (a 1)
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change groupCharacterCupCocycle k G (a 0) (a 1) -
        groupCharacterCupCocycle k G (a 1) (a 0) = 0
      rw [h, sub_self]
    · change a 1 = a 0 at h
      change groupCharacterCupCocycle k G (a 0) (a 1) -
        groupCharacterCupCocycle k G (a 1) (a 0) = 0
      rw [h, sub_self]
    · exact (hij rfl).elim

def groupCharacterSkewExteriorCocycle :
    (⋀[k]^2 (Additive G →+ k)) →ₗ[k]
      groupCohomology.cocycles₂ (groupTrivialCoefficients k G) :=
  exteriorPower.alternatingMapLinearEquiv (groupCharacterSkewAlternatingCocycle k G)

@[simp] theorem groupCharacterSkewExteriorCocycle_wedge
    (χ ψ : Additive G →+ k) :
    groupCharacterSkewExteriorCocycle k G (exteriorWedge (k := k) χ ψ) =
      groupCharacterCupCocycle k G χ ψ - groupCharacterCupCocycle k G ψ χ := by
  simp [groupCharacterSkewExteriorCocycle, exteriorWedge,
    groupCharacterSkewAlternatingCocycle]

@[simp] theorem groupCharacterSkewExteriorCocycle_wedge_apply
    (χ ψ : Additive G →+ k) (g h : G) :
    groupCharacterSkewExteriorCocycle k G (exteriorWedge (k := k) χ ψ) (g, h) =
      χ (Additive.ofMul g) * ψ (Additive.ofMul h) -
        ψ (Additive.ofMul g) * χ (Additive.ofMul h) := by
  rw [groupCharacterSkewExteriorCocycle_wedge]
  rfl

/-- An identity of the whole original exterior maps, with the native
bar quotient and exact scalar coefficient. -/
theorem groupCharacterSkewExteriorCocycle_native_class_map :
    (groupCohomology.H2π (groupTrivialCoefficients k G)).hom.comp
        (groupCharacterSkewExteriorCocycle k G) =
      (2 : k) • groupCharacterQuadraticCup k G := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  have ha : a = ![a 0, a 1] := by
    ext i
    fin_cases i <;> rfl
  rw [ha]
  have hw : (groupCohomology.H2π (groupTrivialCoefficients k G)).hom
      (groupCharacterSkewExteriorCocycle k G (exteriorWedge (k := k) (a 0) (a 1))) =
      (2 : k) • groupCharacterQuadraticCup k G
        (exteriorWedge (k := k) (a 0) (a 1)) := by
    rw [groupCharacterSkewExteriorCocycle_wedge]
    exact groupCharacterSkewCocycle_class_eq_two_cup k G (a 0) (a 1)
  simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, exteriorWedge] using hw

end ChenRanks
