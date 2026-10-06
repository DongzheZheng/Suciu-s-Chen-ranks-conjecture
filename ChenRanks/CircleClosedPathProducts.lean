import ChenRanks.CirclePathLiftIncrementFormula
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Integer winding of products of original closed circle paths

Actual covering lifts give the real endpoint differences. Genuine
closedness cancels the selected argument terms, so the lift of the
actual product gives additivity of the actual integer. Closedness is
retained explicitly; open-path branch corrections are not discarded.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- For a genuine closed path, every genuine lift computes the actual
integer by the actual real endpoint difference. -/
theorem circlePathIntegerIncrement_mul_period_eq_closed_lift_difference
    (γ : C(I, Circle)) (hγ : γ 0 = γ 1) (θ : C(I, ℝ))
    (hθ : ∀ t, Circle.exp (θ t) = γ t) :
    (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi) = θ 1 - θ 0 := by
  have h := circlePathIntegerIncrement_mul_period_eq_lift_difference γ θ hθ
  rw [hγ] at h
  linarith

/-- The winding integer is additive for the actual product of two actual closed paths. -/
theorem circlePathIntegerIncrement_mul_closed
    (γ δ : C(I, Circle)) (hγ : γ 0 = γ 1) (hδ : δ 0 = δ 1) :
    circlePathIntegerIncrement (γ * δ) =
      circlePathIntegerIncrement γ + circlePathIntegerIncrement δ := by
  let θ : C(I, ℝ) := circlePathArgumentLift γ + circlePathArgumentLift δ
  have hθ (t : I) : Circle.exp (θ t) = (γ * δ) t := by
    change Circle.exp (circlePathArgumentLift γ t + circlePathArgumentLift δ t) = γ t * δ t
    rw [Circle.exp_add, circlePathArgumentLift_projects, circlePathArgumentLift_projects]
  have hprod : (γ * δ) 0 = (γ * δ) 1 := by
    change γ 0 * δ 0 = γ 1 * δ 1
    rw [hγ, hδ]
  have h := circlePathIntegerIncrement_mul_period_eq_closed_lift_difference
    (γ * δ) hprod θ hθ
  have hg := circlePathIntegerIncrement_mul_period_eq_closed_lift_difference γ hγ
    (circlePathArgumentLift γ) (circlePathArgumentLift_projects γ)
  have hd := circlePathIntegerIncrement_mul_period_eq_closed_lift_difference δ hδ
    (circlePathArgumentLift δ) (circlePathArgumentLift_projects δ)
  change (circlePathIntegerIncrement (γ * δ) : ℝ) * (2 * Real.pi) =
    (circlePathArgumentLift γ 1 + circlePathArgumentLift δ 1) -
      (circlePathArgumentLift γ 0 + circlePathArgumentLift δ 0) at h
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add]
  apply mul_right_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)
  linarith

/-- The actual constant loop has actual winding zero. -/
theorem circlePathIntegerIncrement_const (z : Circle) :
    circlePathIntegerIncrement (ContinuousMap.const I z) = 0 := by
  let θ : C(I, ℝ) := .const _ (Complex.arg z)
  have h := circlePathIntegerIncrement_mul_period_eq_closed_lift_difference
    (ContinuousMap.const I z) rfl θ (fun _ => Circle.exp_arg z)
  change (circlePathIntegerIncrement (ContinuousMap.const I z) : ℝ) * (2 * Real.pi) =
    Complex.arg z - Complex.arg z at h
  rw [sub_self] at h
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero]
  exact (mul_eq_zero.mp h).resolve_right (by positivity : (2 : ℝ) * Real.pi ≠ 0)

end ChenRanks
