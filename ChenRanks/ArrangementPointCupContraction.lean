import ChenRanks.ArrangementPointMeridianCupPairing
import ChenRanks.ArrangementEquationQuadraticCup
import ChenRanks.KoszulPointContraction

/-!
# Native cup detection by actual point-incidence contraction

The cycle is constructed in the original complement. Its actual cup
evaluation equals the actual exterior contraction by the incidence
functional, on the whole exterior square. In particular, genuine
singular cup relations satisfy all these original point constraints.
No cohomology spanning, relation-kernel comparison, or cycle model is
assumed.
-/

noncomputable section
open scoped BigOperators

namespace ChenRanks.AffineArrangement
open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- The genuine linear functional summing the original incident coefficients. -/
def pointIncidentCoefficientFunctional (x : Fin d → ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ :=
  ∑ K, if A.normal K x = A.offset K then LinearMap.proj K else 0

@[simp] theorem pointIncidentCoefficientFunctional_apply
    (x : Fin d → ℂ) (a : ι → ℂ) :
    A.pointIncidentCoefficientFunctional x a = A.pointIncidentCoefficientSum x a := by
  simp only [pointIncidentCoefficientFunctional, LinearMap.sum_apply,
    pointIncidentCoefficientSum]
  apply Finset.sum_congr rfl
  intro K _
  split_ifs <;> rfl

/-- Equality of actual linear maps, including nondecomposable exterior vectors. -/
theorem actualPointMeridianSquare_cupEvaluation_eq_contraction
    (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) :
    (cycleEvaluation ℂ A.Complement 1
      (periodicSquareChain A.Complement ℂ (A.actualPointMeridianSquare x H))
      (A.boundary_actualPointMeridianSquare_eq_zero x H)).comp A.equationQuadraticCup =
      (LinearMap.proj H.val).comp
        (Koszul.pointDeltaTwo ℂ (ι → ℂ) (A.pointIncidentCoefficientFunctional x)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : exteriorPower.ιMulti ℂ 2 v = exteriorWedge (v 0) (v 1) := by
    change exteriorPower.ιMulti ℂ 2 v = exteriorPower.ιMulti ℂ 2 ![v 0, v 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  change cycleEvaluation ℂ A.Complement 1
      (periodicSquareChain A.Complement ℂ (A.actualPointMeridianSquare x H))
      (A.boundary_actualPointMeridianSquare_eq_zero x H)
      (A.equationQuadraticCup (exteriorPower.ιMulti ℂ 2 v)) =
    (Koszul.pointDeltaTwo ℂ (ι → ℂ) (A.pointIncidentCoefficientFunctional x)
      (exteriorPower.ιMulti ℂ 2 v)) H.val
  rw [hv, A.equationQuadraticCup_exteriorWedge,
    A.actualPointMeridianSquare_coefficientCup, Koszul.pointDeltaTwo_wedge]
  simp only [pointIncidentCoefficientFunctional_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Every actual singular cup relation has zero actual incident contraction
coordinate at every original affine point and incident hyperplane. -/
theorem equationQuadraticCupKernel_point_contraction_eq_zero
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hz : z ∈ A.equationQuadraticCupKernel)
    (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) :
    (Koszul.pointDeltaTwo ℂ (ι → ℂ) (A.pointIncidentCoefficientFunctional x) z) H.val = 0 := by
  have hcup : A.equationQuadraticCup z = 0 := hz
  have heq := DFunLike.congr_fun
    (A.actualPointMeridianSquare_cupEvaluation_eq_contraction x H) z
  change cycleEvaluation ℂ A.Complement 1
      (periodicSquareChain A.Complement ℂ (A.actualPointMeridianSquare x H))
      (A.boundary_actualPointMeridianSquare_eq_zero x H)
      (A.equationQuadraticCup z) =
    (Koszul.pointDeltaTwo ℂ (ι → ℂ) (A.pointIncidentCoefficientFunctional x) z) H.val at heq
  rw [hcup, map_zero] at heq
  exact heq.symm

end ChenRanks.AffineArrangement
