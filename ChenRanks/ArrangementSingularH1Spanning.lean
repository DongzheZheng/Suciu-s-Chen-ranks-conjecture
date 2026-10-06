import ChenRanks.ArrangementMeridianLoopGeneration
import ChenRanks.ArrangementFirstCohomologyLoopDetection
import ChenRanks.ArrangementMeridianClassIndependence

/-!
# Equation classes span singular first cohomology

The meridian-loop theorem applies to a closed singular cochain and proves
that meridian evaluations detect first-cohomology classes. The left
inverse of the equation-class map is consequently a two-sided inverse.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem singularH1_eq_zero_of_actualMeridianEvaluation_eq_zero
    (h : A.singularH1) (hh : A.actualMeridianEvaluationMap h = 0) : h = 0 := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective ℂ A.Complement 1 h
  apply (A.singularH1_eq_zero_iff_all_actual_closed_path_evaluations _).mpr
  intro γ hγ
  rw [closedPathEvaluation_cocycleClass]
  apply A.normalized_closedOne_all_actual_loop_values_eq_zero ℂ
    (cocycleCochain ℂ A.Complement 1 a)
    (cocycleCochain_closed ℂ A.Complement 1 a)
  · intro H
    have hH := congrFun hh H
    change closedPathEvaluation ℂ A.Complement
        (A.meridianDiskPathMap H (A.actualMeridianDisk H))
        (A.meridianDiskPathMap_endpoints H (A.actualMeridianDisk H))
        (cocycleClass ℂ A.Complement 1 a) = 0 at hH
    rw [closedPathEvaluation_cocycleClass] at hH
    exact hH
  · exact hγ

theorem equationWindingClassMap_actualMeridianEvaluationMap
    (h : A.singularH1) :
    A.equationWindingClassMap (A.actualMeridianEvaluationMap h) = h := by
  have hz : A.actualMeridianEvaluationMap
      (h - A.equationWindingClassMap (A.actualMeridianEvaluationMap h)) = 0 := by
    rw [map_sub, A.actualMeridianEvaluationMap_equationWindingClassMap, sub_self]
  exact (sub_eq_zero.mp
    (A.singularH1_eq_zero_of_actualMeridianEvaluation_eq_zero _ hz)).symm

theorem actualMeridianEvaluationMap_injective :
    Function.Injective A.actualMeridianEvaluationMap :=
  (show Function.LeftInverse A.equationWindingClassMap A.actualMeridianEvaluationMap from
    A.equationWindingClassMap_actualMeridianEvaluationMap).injective

theorem equationWindingClassMap_surjective :
    Function.Surjective A.equationWindingClassMap := by
  intro h
  exact ⟨A.actualMeridianEvaluationMap h,
    A.equationWindingClassMap_actualMeridianEvaluationMap h⟩

/-- The original coefficient space is equivalent to actual native H¹. -/
def equationWindingClassEquiv : (ι → ℂ) ≃ₗ[ℂ] A.singularH1 :=
  LinearEquiv.ofBijective A.equationWindingClassMap
    ⟨A.equationWindingClassMap_injective, A.equationWindingClassMap_surjective⟩

@[simp] theorem equationWindingClassEquiv_apply (a : ι → ℂ) :
    A.equationWindingClassEquiv a = A.equationWindingClassMap a := rfl

instance actualSingularH1_finiteDimensional : FiniteDimensional ℂ A.singularH1 :=
  FiniteDimensional.of_injective A.actualMeridianEvaluationMap
    A.actualMeridianEvaluationMap_injective

theorem actualSingularH1_finrank : Module.finrank ℂ A.singularH1 = Fintype.card ι := by
  rw [← A.equationWindingClassEquiv.finrank_eq]
  simp

end ChenRanks.AffineArrangement
