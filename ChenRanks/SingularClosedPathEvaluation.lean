import ChenRanks.SingularPathCycles

/-!
# Evaluation of actual singular cohomology on actual closed paths

Evaluation is first taken in the original singular chain module. The
proved vanishing of native coboundaries on a genuine loop descends this
functional through the native cocycle quotient and its genuine homology
comparison. No homology/cohomology pairing is supplied as a hypothesis.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- Actual cocycle evaluation on the original singular simplex of a path. -/
def pathCocycleEvaluation (γ : C(I, X)) : cocycles k X 1 →ₗ[k] k where
  toFun a := values k X 1 (cocycleCochain k X 1 a) (simplexOfPath X γ)
  map_add' a b := by simp only [map_add, Pi.add_apply]
  map_smul' c a := by simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The genuine native boundary submodule vanishes for an actual closed path. -/
theorem boundaries_le_ker_pathCocycleEvaluation (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    boundaries k X 1 ≤ LinearMap.ker (pathCocycleEvaluation k X γ) := by
  intro a ha
  exact cocycleClass_eq_zero_values_closed_path X k a
    ((cocycleClass_eq_zero_iff k X 1 a).mpr ha) γ hγ

/-- Actual cohomology evaluation on a genuine loop, via the native quotient. -/
def closedPathEvaluation (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    cohomology k X 1 →ₗ[k] k :=
  ((boundaries k X 1).liftQ (pathCocycleEvaluation k X γ)
    (boundaries_le_ker_pathCocycleEvaluation k X γ hγ)).comp
      (representativesEquiv k X 1).toLinearMap

/-- On genuine representatives this is exactly evaluation in the original chains. -/
theorem closedPathEvaluation_cocycleClass (γ : C(I, X)) (hγ : γ 0 = γ 1)
    (a : cocycles k X 1) :
    closedPathEvaluation k X γ hγ (cocycleClass k X 1 a) =
      values k X 1 (cocycleCochain k X 1 a) (simplexOfPath X γ) := by
  change (boundaries k X 1).liftQ (pathCocycleEvaluation k X γ)
    (boundaries_le_ker_pathCocycleEvaluation k X γ hγ)
      ((representativesEquiv k X 1)
        ((representativesEquiv k X 1).symm ((boundaries k X 1).mkQ a))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ChenRanks.SingularCohomology
