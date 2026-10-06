import ChenRanks.ArrangementMeridianLoopGeneration
import ChenRanks.ArrangementFirstCohomologyLoopDetection
import ChenRanks.ArrangementMeridianClassIndependence

/-!
# Actual first cohomology over the coefficient field

The equation classes and meridian evaluations are defined on the actual
singular cohomology over the original coefficient field. The geometric
closed-loop detection theorem was already proved for this field, so it
gives the same genuine basis over the rationals as over the complexes.
This supplies rational first-cohomology data for the manuscript's rational
Chen space without assuming scalar-extension or formality comparisons.
It does not identify rational Chen ranks with a Koszul module.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open scoped BigOperators

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (k : Type) [Field k]

/-- Original equation classes with the actual coefficient field. -/
def fieldEquationClassMap : (ι → k) →ₗ[k] cohomology k A.Complement 1 where
  toFun a := ∑ H, a H • A.equationWindingClass k H
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]

/-- Evaluation on the same actual canonical geometric meridians. -/
def fieldMeridianEvaluationMap : cohomology k A.Complement 1 →ₗ[k] (ι → k) :=
  LinearMap.pi (fun H => closedPathEvaluation k A.Complement
    (A.meridianDiskPathMap H (A.actualMeridianDisk H))
    (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H)))

theorem fieldMeridianEvaluationMap_equationClassMap (a : ι → k) :
    A.fieldMeridianEvaluationMap k (A.fieldEquationClassMap k a) = a := by
  classical
  funext H
  change closedPathEvaluation k A.Complement
    (A.meridianDiskPathMap H (A.actualMeridianDisk H))
    (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))
    (∑ K, a K • A.equationWindingClass k K) = a H
  rw [map_sum]
  simp only [map_smul, A.closedPathEvaluation_equationWindingClass]
  simp [A.actualMeridianPathMap_equation_increment]

theorem fieldSingularH1_eq_zero_of_meridianEvaluation_eq_zero
    (h : cohomology k A.Complement 1) (hh : A.fieldMeridianEvaluationMap k h = 0) :
    h = 0 := by
  letI := A.complement_pathConnectedSpace_from_actual_equations
  obtain ⟨β, rfl⟩ := cocycleClass_surjective k A.Complement 1 h
  apply (firstCohomology_eq_zero_iff_closed_path_evaluations A.Complement k _).mpr
  intro γ hγ
  rw [closedPathEvaluation_cocycleClass]
  apply A.normalized_closedOne_all_actual_loop_values_eq_zero k
    (cocycleCochain k A.Complement 1 β)
    (cocycleCochain_closed k A.Complement 1 β)
  · intro H
    have hH := congrFun hh H
    change closedPathEvaluation k A.Complement
      (A.meridianDiskPathMap H (A.actualMeridianDisk H))
      (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))
      (cocycleClass k A.Complement 1 β) = 0 at hH
    rw [closedPathEvaluation_cocycleClass] at hH
    exact hH
  · exact hγ

theorem fieldEquationClassMap_meridianEvaluationMap
    (h : cohomology k A.Complement 1) :
    A.fieldEquationClassMap k (A.fieldMeridianEvaluationMap k h) = h := by
  have hz : A.fieldMeridianEvaluationMap k
      (h - A.fieldEquationClassMap k (A.fieldMeridianEvaluationMap k h)) = 0 := by
    rw [map_sub, A.fieldMeridianEvaluationMap_equationClassMap, sub_self]
  exact (sub_eq_zero.mp (A.fieldSingularH1_eq_zero_of_meridianEvaluation_eq_zero k _ hz)).symm

/-- A genuine coefficient-to-native-H¹ equivalence, including k = Q. -/
def fieldEquationClassEquiv : (ι → k) ≃ₗ[k] cohomology k A.Complement 1 :=
  LinearEquiv.ofBijective (A.fieldEquationClassMap k)
    ⟨(show Function.LeftInverse (A.fieldMeridianEvaluationMap k)
        (A.fieldEquationClassMap k) from
          A.fieldMeridianEvaluationMap_equationClassMap k).injective,
      fun h => ⟨A.fieldMeridianEvaluationMap k h,
        A.fieldEquationClassMap_meridianEvaluationMap k h⟩⟩

instance actualFieldSingularH1_finiteDimensional :
    FiniteDimensional k (cohomology k A.Complement 1) :=
  FiniteDimensional.of_injective (A.fieldMeridianEvaluationMap k)
    (show Function.LeftInverse (A.fieldEquationClassMap k)
      (A.fieldMeridianEvaluationMap k) from
        A.fieldEquationClassMap_meridianEvaluationMap k).injective

theorem actualFieldSingularH1_finrank :
    Module.finrank k (cohomology k A.Complement 1) = Fintype.card ι := by
  rw [← (A.fieldEquationClassEquiv k).finrank_eq]
  simp

end ChenRanks.AffineArrangement
