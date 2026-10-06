import ChenRanks.ArrangementLogarithmicMeridianPeriods
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Genuine off-diagonal logarithmic meridian periods

An original hyperplane equation other than the distinguished equation
is nonzero on the entire actual transverse disk, by the proved original
disk-avoidance theorem.  Its reciprocal pullback is genuinely holomorphic
there.  Native Cauchy-Goursat gives its zero actual logarithmic period.
This is a calculation of actual integrals on actual meridians, not an
assumed de Rham comparison or an identification of all smooth cohomology.
-/

noncomputable section

open Complex MeasureTheory

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual pullback of an original equation to the genuine original
transverse disk, retaining the actual affine offset. -/
theorem meridianDisk_otherAffineEquation
    (H K : ι) (m : A.MeridianDisk H) (z : ℂ) :
    A.actualAffineEquationFunction K (m.center + z • m.normalVector) =
      (A.normal K m.center - A.offset K) + z * A.normal K m.normalVector := by
  unfold actualAffineEquationFunction
  rw [map_add, map_smul, smul_eq_mul]
  ring

/-- The actual off-diagonal disk pullback has no zero anywhere on the
actual closed disk; no nonvanishing premise is supplied. -/
theorem meridianDisk_otherAffineEquation_ne_zero_on_closedBall
    (H K : ι) (m : A.MeridianDisk H) (hKH : K ≠ H)
    (z : ℂ) (hz : z ∈ Metric.closedBall 0 m.radius) :
    (A.normal K m.center - A.offset K) + z * A.normal K m.normalVector ≠ 0 := by
  rw [← A.meridianDisk_otherAffineEquation H K m z]
  exact sub_ne_zero.mpr (m.disk_avoids z
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) K hKH)

/-- Genuine disk pullback of the other original logarithmic one-form. -/
theorem meridianDisk_otherLogarithmicForm_tangent
    (H K : ι) (m : A.MeridianDisk H) (z w : ℂ) :
    A.actualAmbientLogarithmicOneForm K (m.center + z • m.normalVector)
      (fun _ : Fin 1 => w • m.normalVector) =
      ((A.normal K m.center - A.offset K) + z * A.normal K m.normalVector)⁻¹ *
        (w * A.normal K m.normalVector) := by
  rw [actualAmbientLogarithmicOneForm_apply]
  change (A.actualAffineEquationFunction K (m.center + z • m.normalVector))⁻¹ *
    A.normal K (w • m.normalVector) = _
  rw [meridianDisk_otherAffineEquation, map_smul, smul_eq_mul]

/-- The genuine integral of the other original logarithm along the
already constructed distinguished meridian. -/
def actualOtherLogarithmicMeridianIntegral
    (H K : ι) (m : A.MeridianDisk H) : ℂ :=
  ∫ θ : ℝ in 0..2 * Real.pi,
    A.actualAmbientLogarithmicOneForm K (A.meridianDiskAngleAmbientMap H m θ)
      (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector)

/-- Native Cauchy-Goursat on the actual nonvanishing original disk proves
the actual off-diagonal meridian period vanishes. -/
theorem actualOtherLogarithmicMeridianIntegral_eq_zero
    (H K : ι) (m : A.MeridianDisk H) (hKH : K ≠ H) :
    A.actualOtherLogarithmicMeridianIntegral H K m = 0 := by
  let a : ℂ := A.normal K m.center - A.offset K
  let b : ℂ := A.normal K m.normalVector
  let f : ℂ → ℂ := fun z => b * (a + z * b)⁻¹
  have hne (z : ℂ) (hz : z ∈ Metric.closedBall 0 m.radius) : a + z * b ≠ 0 :=
    A.meridianDisk_otherAffineEquation_ne_zero_on_closedBall H K m hKH z hz
  have hc : ContinuousOn f (Metric.closedBall 0 m.radius) :=
    continuousOn_const.mul ((continuousOn_const.add
      (continuousOn_id.mul continuousOn_const)).inv₀ hne)
  have hd (z : ℂ) (hz : z ∈ Metric.ball 0 m.radius \ (∅ : Set ℂ)) :
      DifferentiableAt ℂ f z := by
    have hdz : HasDerivAt (fun z : ℂ => a + z * b) b z :=
      by simpa only [one_mul] using (hasDerivAt_id z |>.mul_const b).const_add a
    exact (hdz.inv (hne z (Metric.ball_subset_closedBall hz.1))).differentiableAt.const_mul b
  have hi : circleIntegral f 0 m.radius = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      m.radius_pos.le Set.countable_empty hc hd
  have he : A.actualOtherLogarithmicMeridianIntegral H K m =
      circleIntegral f 0 m.radius := by
    unfold actualOtherLogarithmicMeridianIntegral circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    change A.actualAmbientLogarithmicOneForm K
      (m.center + circleMap 0 m.radius θ • m.normalVector)
      (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector) = _
    rw [meridianDisk_otherLogarithmicForm_tangent]
    change (a + circleMap 0 m.radius θ * b)⁻¹ *
      (deriv (circleMap 0 m.radius) θ * b) =
      deriv (circleMap 0 m.radius) θ * (b * (a + circleMap 0 m.radius θ * b)⁻¹)
    ring
  exact he.trans hi

end ChenRanks.AffineArrangement
