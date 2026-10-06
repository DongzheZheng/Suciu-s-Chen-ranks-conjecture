import ChenRanks.SingularCupCocycleDescent
import ChenRanks.ExteriorSeparation

/-!
# Alternation of the actual singular cup product

The explicit original one-cochain homotopy gives skew-commutativity on
the original native singular cohomology. In characteristic zero the
bilinear product is alternating, and the native exterior-power universal
property supplies the actual quadratic cup map and its actual kernel.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The sum of the two actual products of cocycle representatives is an actual boundary. -/
theorem cocycleCup_add_swap_mem_boundaries (a b : cocycles k X 1) :
    cocycleCup k X a b + cocycleCup k X b a ∈ boundaries k X 2 := by
  apply (mem_positive_boundaries_iff k X 1 _).mpr
  refine ⟨-(edgePointProduct k X (cocycleCochain k X 1 a)
    (cocycleCochain k X 1 b)), ?_⟩
  rw [map_neg, differential_edgePointProduct k X _ _
    (cocycleCochain_closed k X 1 a) (cocycleCochain_closed k X 1 b), neg_neg,
    map_add, cocycleCochain_cocycleCup, cocycleCochain_cocycleCup]

/-- The actual original cohomology cup is skew-commutative in degree one. -/
theorem cup_add_swap (a b : cohomology k X 1) :
    cup k X a b + cup k X b a = 0 := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective k X 1 a
  obtain ⟨b, rfl⟩ := cocycleClass_surjective k X 1 b
  rw [cup_cocycleClass, cup_cocycleClass, ← map_add]
  exact (cocycleClass_eq_zero_iff k X 2 _).mpr
    (cocycleCup_add_swap_mem_boundaries k X a b)

variable [CharZero k]

/-- Alternation of the original degree-one cup follows from the actual
homotopy and the invertibility of two in the original coefficient field. -/
theorem cup_self_eq_zero (a : cohomology k X 1) : cup k X a a = 0 := by
  have h := cup_add_swap k X a a
  have htwo : (2 : k) • cup k X a a = 0 := by
    simpa only [two_smul] using h
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- The true alternating degree-one cup, on two original cohomology classes. -/
def alternatingCup :
    (cohomology k X 1) [⋀^Fin 2]→ₗ[k] (cohomology k X 2) where
  toFun a := cup k X (a 0) (a 1)
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change cup k X (a 0) (a 1) = 0
      rw [h]
      exact cup_self_eq_zero k X (a 1)
    · change a 1 = a 0 at h
      change cup k X (a 0) (a 1) = 0
      rw [h]
      exact cup_self_eq_zero k X (a 0)
    · exact (hij rfl).elim

/-- The actual exterior-square cup map on original singular cohomology. -/
def quadraticCup : (⋀[k]^2 (cohomology k X 1)) →ₗ[k] cohomology k X 2 :=
  exteriorPower.alternatingMapLinearEquiv (alternatingCup k X)

/-- The actual exterior-square map is precisely the genuine cup product on decomposable classes. -/
theorem quadraticCup_exteriorWedge (a b : cohomology k X 1) :
    quadraticCup k X (exteriorWedge (k := k) a b) = cup k X a b := by
  simp [quadraticCup, exteriorWedge, alternatingCup]

/-- The actual quadratic kernel of the original singular cohomology cup. -/
def quadraticCupKernel : Submodule k (⋀[k]^2 (cohomology k X 1)) :=
  LinearMap.ker (quadraticCup k X)

end ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original complement's actual degree-one singular cup product. -/
abbrev singularCup : A.singularH1 →ₗ[ℂ] A.singularH1 →ₗ[ℂ] A.singularH2 :=
  SingularCohomology.cup ℂ A.Complement

/-- The actual quadratic cup map of the original arrangement complement. -/
abbrev quadraticSingularCup : (⋀[ℂ]^2 A.singularH1) →ₗ[ℂ] A.singularH2 :=
  SingularCohomology.quadraticCup ℂ A.Complement

/-- The actual original singular cup kernel, before the logarithmic comparison theorem. -/
abbrev singularCupKernel : Submodule ℂ (⋀[ℂ]^2 A.singularH1) :=
  SingularCohomology.quadraticCupKernel ℂ A.Complement

end ChenRanks.AffineArrangement
