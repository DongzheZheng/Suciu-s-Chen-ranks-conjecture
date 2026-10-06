import ChenRanks.SingularCupDifferentialIdentities
import ChenRanks.SingularCocycleCochains
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Descent of the genuine singular cup product

The bilinear product on original closed cochains is placed in the native
cocycle modules. The two actual boundary identities prove vanishing on
the native boundary submodules in both variables. The native bilinear
quotient construction then defines the cup product on the original
singular cohomology objects, with its exact representative formula.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The original cup product, as a bilinear map on genuine native cocycles. -/
def cocycleCup : cocycles k X 1 →ₗ[k] cocycles k X 1 →ₗ[k] cocycles k X 2 where
  toFun a :=
    { toFun := fun b =>
        toCocycle k X 2
          (cupOne k X (cocycleCochain k X 1 a) (cocycleCochain k X 1 b))
          (differential_cupOne_eq_zero k X _ _
            (cocycleCochain_closed k X 1 a) (cocycleCochain_closed k X 1 b))
      map_add' := by
        intro b c
        apply Subtype.ext
        change cupOne k X _ (cocycleCochain k X 1 (b + c)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro c b
        apply Subtype.ext
        change cupOne k X _ (cocycleCochain k X 1 (c • b)) = _
        rw [map_smul, map_smul]
        rfl }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change cupOne k X (cocycleCochain k X 1 (a + b)) _ = _
    rw [map_add, map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    change cupOne k X (cocycleCochain k X 1 (c • a)) _ = _
    rw [map_smul, map_smul, LinearMap.smul_apply]
    rfl

/-- The actual underlying cochain of the native cocycle product. -/
theorem cocycleCochain_cocycleCup (a b : cocycles k X 1) :
    cocycleCochain k X 2 (cocycleCup k X a b) =
      cupOne k X (cocycleCochain k X 1 a) (cocycleCochain k X 1 b) := rfl

/-- The actual product class before descending its two input variables. -/
def cupClassOnCocycles : cocycles k X 1 →ₗ[k] cocycles k X 1 →ₗ[k] cohomology k X 2 :=
  (cocycleCup k X).compr₂ (cocycleClass k X 2)

/-- A genuine boundary in the first variable gives the zero actual product class. -/
theorem cupClassOnCocycles_eq_zero_of_left_boundary
    (a b : cocycles k X 1) (ha : a ∈ boundaries k X 1) :
    cupClassOnCocycles k X a b = 0 := by
  obtain ⟨f, hf⟩ := (mem_positive_boundaries_iff k X 0 a).mp ha
  apply (cocycleClass_eq_zero_iff k X 2 (cocycleCup k X a b)).mpr
  apply (mem_positive_boundaries_iff k X 1 (cocycleCup k X a b)).mpr
  refine ⟨cupZeroOne k X f (cocycleCochain k X 1 b), ?_⟩
  rw [differential_cupZeroOne k X f _ (cocycleCochain_closed k X 1 b),
    hf, cocycleCochain_cocycleCup]

/-- A genuine boundary in the second variable also gives the zero actual product class. -/
theorem cupClassOnCocycles_eq_zero_of_right_boundary
    (a b : cocycles k X 1) (hb : b ∈ boundaries k X 1) :
    cupClassOnCocycles k X a b = 0 := by
  obtain ⟨f, hf⟩ := (mem_positive_boundaries_iff k X 0 b).mp hb
  apply (cocycleClass_eq_zero_iff k X 2 (cocycleCup k X a b)).mpr
  apply (mem_positive_boundaries_iff k X 1 (cocycleCup k X a b)).mpr
  refine ⟨-(cupOneZero k X (cocycleCochain k X 1 a) f), ?_⟩
  rw [map_neg, differential_cupOneZero k X _ f (cocycleCochain_closed k X 1 a),
    neg_neg, hf, cocycleCochain_cocycleCup]

/-- The actual boundary submodule is killed in the first input. -/
theorem boundaries_le_ker_cupClassOnCocycles :
    boundaries k X 1 ≤ LinearMap.ker (cupClassOnCocycles k X) := by
  intro a ha
  apply LinearMap.ext
  intro b
  exact cupClassOnCocycles_eq_zero_of_left_boundary k X a b ha

/-- The same actual boundary submodule is killed in the second input. -/
theorem boundaries_le_ker_flip_cupClassOnCocycles :
    boundaries k X 1 ≤ LinearMap.ker (cupClassOnCocycles k X).flip := by
  intro b hb
  apply LinearMap.ext
  intro a
  exact cupClassOnCocycles_eq_zero_of_right_boundary k X a b hb

/-- The genuine bilinear cup product on the two native cocycle quotients. -/
def cupOnCocycleQuotients :
    cocycleQuotient k X 1 →ₗ[k] cocycleQuotient k X 1 →ₗ[k] cohomology k X 2 :=
  (cupClassOnCocycles k X).liftQ₂ (boundaries k X 1) (boundaries k X 1)
    (boundaries_le_ker_cupClassOnCocycles k X)
    (boundaries_le_ker_flip_cupClassOnCocycles k X)

/-- The genuine cup product on the original native singular cohomology objects. -/
def cup : cohomology k X 1 →ₗ[k] cohomology k X 1 →ₗ[k] cohomology k X 2 :=
  (cupOnCocycleQuotients k X).compl₁₂
    (representativesEquiv k X 1).toLinearMap (representativesEquiv k X 1).toLinearMap

/-- The actual cohomology cup product has exactly the original closed-cochain product class. -/
theorem cup_cocycleClass (a b : cocycles k X 1) :
    cup k X (cocycleClass k X 1 a) (cocycleClass k X 1 b) =
      cocycleClass k X 2 (cocycleCup k X a b) := by
  change cupOnCocycleQuotients k X
    ((representativesEquiv k X 1)
      ((representativesEquiv k X 1).symm ((boundaries k X 1).mkQ a)))
    ((representativesEquiv k X 1)
      ((representativesEquiv k X 1).symm ((boundaries k X 1).mkQ b))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

end ChenRanks.SingularCohomology
