import ChenRanks.ArrangementSmoothLogarithmicOneForms
import ChenRanks.ArrangementMeridianCircle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Genuine logarithmic periods on the original meridians

The parameterized circle lies in the original complement, and its tangent
is its genuine native derivative.  Pulling back the actual logarithmic
one-form gives `z⁻¹ dz`; the native circle-integral theorem therefore gives
the actual factor `2πi`.  The normalized actual integrand has integral one.
The final equality compares this particular actual period with the
already constructed original meridian winding.  It is not a de Rham
comparison for arbitrary forms or loops, nor a quasi-isomorphism or a
formality assertion.
-/

noncomputable section

open Complex MeasureTheory
open unitInterval

namespace ChenRanks

/-- The actual complex period of the unnormalized logarithmic form. -/
def logarithmicPeriodConstant : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem logarithmicPeriodConstant_ne_zero : logarithmicPeriodConstant ≠ 0 := by
  unfold logarithmicPeriodConstant
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
    Complex.I_ne_zero

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual angular parameterization of the already constructed disk
boundary, using the original center and original normal vector. -/
def meridianDiskAngleAmbientMap (H : ι) (m : A.MeridianDisk H) (θ : ℝ) :
    Fin d → ℂ := m.center + circleMap 0 m.radius θ • m.normalVector

/-- The original equation of the distinguished hyperplane is the genuine
complex disk coordinate, not an assigned winding coordinate. -/
theorem meridianDisk_affineEquation (H : ι) (m : A.MeridianDisk H) (z : ℂ) :
    A.actualAffineEquationFunction H (m.center + z • m.normalVector) = z := by
  unfold actualAffineEquationFunction
  rw [map_add, map_smul, m.center_on, m.normal_value, smul_eq_mul, mul_one]
  exact add_sub_cancel_left _ _

/-- Every point of the actual angular circle remains in the actual
original complement, by the proved disk avoidance and positive radius. -/
theorem meridianDiskAngleAmbientMap_mem_complement
    (H : ι) (m : A.MeridianDisk H) (θ : ℝ) :
    A.meridianDiskAngleAmbientMap H m θ ∈ A.ambientComplementSet := by
  intro K
  by_cases hKH : K = H
  · subst K
    apply sub_ne_zero.mp
    change A.actualAffineEquationFunction H
      (m.center + circleMap 0 m.radius θ • m.normalVector) ≠ 0
    rw [meridianDisk_affineEquation]
    exact circleMap_ne_center m.radius_pos.ne'
  · exact m.disk_avoids (circleMap 0 m.radius θ)
      (by simp only [norm_circleMap_zero, abs_of_pos m.radius_pos]; exact le_rfl) K hKH

/-- Its native derivative is the genuine original meridian tangent. -/
theorem meridianDiskAngleAmbientMap_hasDerivAt
    (H : ι) (m : A.MeridianDisk H) (θ : ℝ) :
    HasDerivAt (A.meridianDiskAngleAmbientMap H m)
      (deriv (circleMap 0 m.radius) θ • m.normalVector) θ := by
  apply hasDerivAt_pi.mpr
  intro i
  change HasDerivAt
    (fun t => m.center i + circleMap 0 m.radius t * m.normalVector i)
    (deriv (circleMap 0 m.radius) θ * m.normalVector i) θ
  simpa only [deriv_circleMap] using
    ((hasDerivAt_circleMap 0 m.radius θ).mul_const (m.normalVector i)).const_add (m.center i)

/-- This is the same original oriented meridian as the one whose genuine
integer winding was constructed through the exponential covering. -/
theorem meridianDiskAngleAmbientMap_eq_original_meridian
    (H : ι) (m : A.MeridianDisk H) (t : I) :
    A.meridianDiskAngleAmbientMap H m ((2 * Real.pi) * (t : ℝ)) =
      (A.meridianDiskPathMap H m t).val := by
  simp only [meridianDiskAngleAmbientMap, meridianDiskPathMap,
    meridianDiskCircleMap, positiveUnitCircleTraversal, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Circle.coe_exp, circleMap_zero]

/-- Evaluation of the actual original one-form on the actual transverse
disk tangent is exactly `z⁻¹ dz`, with no pullback specification premise. -/
theorem meridianDisk_logarithmicForm_tangent
    (H : ι) (m : A.MeridianDisk H) (z w : ℂ) :
    A.actualAmbientLogarithmicOneForm H (m.center + z • m.normalVector)
      (fun _ : Fin 1 => w • m.normalVector) = z⁻¹ * w := by
  rw [actualAmbientLogarithmicOneForm_apply]
  change (A.actualAffineEquationFunction H (m.center + z • m.normalVector))⁻¹ *
    A.normal H (w • m.normalVector) = z⁻¹ * w
  rw [meridianDisk_affineEquation, map_smul, m.normal_value, smul_eq_mul, mul_one]

/-- The genuine native line integral of the original logarithmic form,
over the actual angular parameter and its actual derivative. -/
def actualLogarithmicMeridianIntegral (H : ι) (m : A.MeridianDisk H) : ℂ :=
  ∫ θ : ℝ in 0..2 * Real.pi,
    A.actualAmbientLogarithmicOneForm H (A.meridianDiskAngleAmbientMap H m θ)
      (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector)

/-- The comparison is with the actual native circle integral. -/
theorem actualLogarithmicMeridianIntegral_eq_circleIntegral
    (H : ι) (m : A.MeridianDisk H) :
    A.actualLogarithmicMeridianIntegral H m =
      circleIntegral (fun z : ℂ => z⁻¹) 0 m.radius := by
  unfold actualLogarithmicMeridianIntegral circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  change A.actualAmbientLogarithmicOneForm H
      (m.center + circleMap 0 m.radius θ • m.normalVector)
      (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector) = _
  rw [meridianDisk_logarithmicForm_tangent]
  change (circleMap 0 m.radius θ)⁻¹ * deriv (circleMap 0 m.radius) θ =
    deriv (circleMap 0 m.radius) θ • (circleMap 0 m.radius θ)⁻¹
  rw [smul_eq_mul, mul_comm]

/-- The unnormalized original logarithmic period is genuinely `2πi`. -/
theorem actualLogarithmicMeridianIntegral_eq_two_pi_I
    (H : ι) (m : A.MeridianDisk H) :
    A.actualLogarithmicMeridianIntegral H m = logarithmicPeriodConstant := by
  rw [actualLogarithmicMeridianIntegral_eq_circleIntegral]
  simpa only [sub_zero, logarithmicPeriodConstant] using
    circleIntegral.integral_sub_inv_of_mem_ball
      (c := (0 : ℂ)) (w := (0 : ℂ)) (R := m.radius)
      (by simpa only [Metric.mem_ball, dist_self] using m.radius_pos)

/-- The actual integral of the normalized original logarithmic integrand. -/
def actualNormalizedLogarithmicMeridianIntegral
    (H : ι) (m : A.MeridianDisk H) : ℂ :=
  ∫ θ : ℝ in 0..2 * Real.pi,
    logarithmicPeriodConstant⁻¹ *
      A.actualAmbientLogarithmicOneForm H (A.meridianDiskAngleAmbientMap H m θ)
        (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector)

/-- The normalized actual original form has period one. -/
theorem actualNormalizedLogarithmicMeridianIntegral_eq_one
    (H : ι) (m : A.MeridianDisk H) :
    A.actualNormalizedLogarithmicMeridianIntegral H m = 1 := by
  let f : ℝ → ℂ := fun θ =>
    A.actualAmbientLogarithmicOneForm H (A.meridianDiskAngleAmbientMap H m θ)
      (fun _ : Fin 1 => deriv (circleMap 0 m.radius) θ • m.normalVector)
  have h := intervalIntegral.integral_const_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := MeasureTheory.volume)
    logarithmicPeriodConstant⁻¹ f
  change (∫ θ : ℝ in 0..2 * Real.pi, logarithmicPeriodConstant⁻¹ * f θ) = 1
  refine h.trans ?_
  change logarithmicPeriodConstant⁻¹ * A.actualLogarithmicMeridianIntegral H m = 1
  rw [actualLogarithmicMeridianIntegral_eq_two_pi_I,
    inv_mul_cancel₀ logarithmicPeriodConstant_ne_zero]

/-- A real equality between the actual normalized period and the genuine
native integer winding on this same original meridian. -/
theorem actualNormalizedLogarithmicMeridianIntegral_eq_original_winding
    (H : ι) (m : A.MeridianDisk H) :
    A.actualNormalizedLogarithmicMeridianIntegral H m =
      (circlePathIntegerIncrement
        ((A.equationComplementCircleMap H).comp (A.meridianDiskPathMap H m)) : ℂ) := by
  rw [actualNormalizedLogarithmicMeridianIntegral_eq_one,
    meridianDiskPathMap_distinguished_increment]
  simp

end AffineArrangement
end ChenRanks
