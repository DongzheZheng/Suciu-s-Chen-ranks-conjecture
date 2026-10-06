import ChenRanks.ArrangementPointMeridianPhases
import ChenRanks.ArrangementCentralRadialSquare

/-! True incident-equation integers on the genuinely constructed original localized square. -/

noncomputable section
open unitInterval
namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance : DecidableEq ι := Classical.decEq ι

/-- The true horizontal incident equation path is a genuine circle times a constant phase. -/
theorem actualPointMeridianSquare_horizontal_incident_path (x : Fin d → ℂ)
    (H K : A.PointLocalizedLabels x) :
    (A.equationComplementCircleMap K.val).comp
        (periodicSquareHorizontalPath A.Complement (A.actualPointMeridianSquare x H)) =
      positiveUnitCircleTraversal * (ContinuousMap.const I
        ((A.pointLocalizedArrangement x).equationComplementCircleMap K
          ((A.pointLocalizedArrangement x).meridianDiskPathMap H
            ((A.pointLocalizedArrangement x).actualMeridianDisk H) 0))) := by
  apply ContinuousMap.ext
  intro t
  exact A.actualPointMeridianSquare_incident_phase x H K (t, 0)

/-- The true vertical incident equation path is the original localized meridian equation path. -/
theorem actualPointMeridianSquare_vertical_incident_path (x : Fin d → ℂ)
    (H K : A.PointLocalizedLabels x) :
    (A.equationComplementCircleMap K.val).comp
        (periodicSquareVerticalPath A.Complement (A.actualPointMeridianSquare x H)) =
      ((A.pointLocalizedArrangement x).equationComplementCircleMap K).comp
        ((A.pointLocalizedArrangement x).meridianDiskPathMap H
          ((A.pointLocalizedArrangement x).actualMeridianDisk H)) := by
  apply ContinuousMap.ext
  intro s
  change A.equationComplementCircleMap K.val (A.actualPointMeridianSquare x H (0, s)) = _
  rw [A.actualPointMeridianSquare_incident_phase, positiveUnitCircleTraversal_zero, one_mul]
  rfl

/-- Every incident actual horizontal equation has true integer winding one. -/
theorem actualPointMeridianSquare_horizontal_incident_increment (x : Fin d → ℂ)
    (H K : A.PointLocalizedLabels x) :
    circlePathIntegerIncrement ((A.equationComplementCircleMap K.val).comp
      (periodicSquareHorizontalPath A.Complement (A.actualPointMeridianSquare x H))) = 1 := by
  rw [A.actualPointMeridianSquare_horizontal_incident_path x H K,
    circlePathIntegerIncrement_mul_closed _ _ (by simp) rfl,
    circlePathIntegerIncrement_positiveUnitCircleTraversal,
    circlePathIntegerIncrement_const, add_zero]

/-- The actual vertical incident winding matrix is the true constructed meridian identity. -/
theorem actualPointMeridianSquare_vertical_incident_increment (x : Fin d → ℂ)
    (H K : A.PointLocalizedLabels x) :
    circlePathIntegerIncrement ((A.equationComplementCircleMap K.val).comp
      (periodicSquareVerticalPath A.Complement (A.actualPointMeridianSquare x H))) =
      if K = H then 1 else 0 := by
  rw [A.actualPointMeridianSquare_vertical_incident_path]
  have hnative := (A.pointLocalizedArrangement x).actualMeridianPathMap_equation_increment H K
  by_cases hKH : K = H
  · simpa only [if_pos hKH] using hnative
  · simpa only [if_neg hKH] using hnative

end ChenRanks.AffineArrangement
