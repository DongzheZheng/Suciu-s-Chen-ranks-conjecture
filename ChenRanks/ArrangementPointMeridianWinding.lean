import ChenRanks.ArrangementPointMeridianIncidentWinding
import ChenRanks.ArrangementPointBallWinding

/-!
# The complete actual winding matrix of an original localized square

The incident entries come from the original constructed local meridians.
Every nonincident entry vanishes by the actual straight contraction in
the original proved avoidance ball. No incidence matrix, winding label,
or local cycle is supplied as a hypothesis.
-/

noncomputable section
open unitInterval
namespace ChenRanks.AffineArrangement
open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- The true original horizontal equation integer is precisely actual incidence. -/
theorem actualPointMeridianSquare_horizontal_increment (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (K : ι) :
    circlePathIntegerIncrement ((A.equationComplementCircleMap K).comp
      (periodicSquareHorizontalPath A.Complement (A.actualPointMeridianSquare x H))) =
      if A.normal K x = A.offset K then 1 else 0 := by
  by_cases hKx : A.normal K x = A.offset K
  · rw [if_pos hKx]
    exact A.actualPointMeridianSquare_horizontal_incident_increment x H ⟨K, hKx⟩
  · rw [if_neg hKx]
    apply A.pointBall_equation_increment_zero x K hKx
      (periodicSquareHorizontalPath A.Complement (A.actualPointMeridianSquare x H))
      (periodicSquareHorizontalPath_endpoints A.Complement _
        (A.actualPointMeridianSquare_vertical_periodic x H))
    intro s
    exact A.actualPointMeridianSquare_dist_lt_radius x H (s, 0)

/-- The true original vertical equation matrix is the genuine distinguished meridian identity. -/
theorem actualPointMeridianSquare_vertical_increment (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (K : ι) :
    circlePathIntegerIncrement ((A.equationComplementCircleMap K).comp
      (periodicSquareVerticalPath A.Complement (A.actualPointMeridianSquare x H))) =
      if K = H.val then 1 else 0 := by
  by_cases hKx : A.normal K x = A.offset K
  · have heq : (⟨K, hKx⟩ : A.PointLocalizedLabels x) = H ↔ K = H.val :=
      Subtype.ext_iff
    rw [A.actualPointMeridianSquare_vertical_incident_increment x H ⟨K, hKx⟩]
    simp only [heq]
  · have hKH : K ≠ H.val := by
      intro h
      subst K
      exact hKx H.property
    rw [if_neg hKH]
    apply A.pointBall_equation_increment_zero x K hKx
      (periodicSquareVerticalPath A.Complement (A.actualPointMeridianSquare x H))
      (periodicSquareVerticalPath_endpoints A.Complement _
        (A.actualPointMeridianSquare_horizontal_periodic x H))
    intro s
    exact A.actualPointMeridianSquare_dist_lt_radius x H (0, s)

end ChenRanks.AffineArrangement
