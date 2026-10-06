import ChenRanks.CircleClosedPathProducts

/-!
# The actual argument correction for a product of open circle paths

The selected principal arguments need not add. Their integer discrepancy
is retained as a genuine endpoint correction. This supplies a zero-cochain
primitive when winding classes are pulled back along a product of circle maps.
-/

noncomputable section

open unitInterval

namespace ChenRanks

theorem circleProductArgumentCarry_exists (z w : Circle) :
    ∃ n : ℤ, Complex.arg z + Complex.arg w =
      Complex.arg (z * w) + (n : ℝ) * (2 * Real.pi) := by
  apply Circle.exp_eq_exp.mp
  rw [Circle.exp_add, Circle.exp_arg, Circle.exp_arg]
  exact (Circle.exp_arg (z * w)).symm

/-- The integer discrepancy of the actual selected arguments. -/
def circleProductArgumentCarry (z w : Circle) : ℤ :=
  (circleProductArgumentCarry_exists z w).choose

theorem circleProductArgumentCarry_formula (z w : Circle) :
    Complex.arg z + Complex.arg w = Complex.arg (z * w) +
      (circleProductArgumentCarry z w : ℝ) * (2 * Real.pi) :=
  (circleProductArgumentCarry_exists z w).choose_spec

/-- Open paths have an actual endpoint correction; no closedness is assumed. -/
theorem circlePathIntegerIncrement_mul (γ δ : C(I, Circle)) :
    circlePathIntegerIncrement (γ * δ) =
      circlePathIntegerIncrement γ + circlePathIntegerIncrement δ +
        circleProductArgumentCarry (γ 1) (δ 1) -
        circleProductArgumentCarry (γ 0) (δ 0) := by
  let θ : C(I, ℝ) := circlePathArgumentLift γ + circlePathArgumentLift δ
  have hθ (t : I) : Circle.exp (θ t) = (γ * δ) t := by
    change Circle.exp (circlePathArgumentLift γ t + circlePathArgumentLift δ t) =
      γ t * δ t
    rw [Circle.exp_add, circlePathArgumentLift_projects, circlePathArgumentLift_projects]
  have h := circlePathIntegerIncrement_mul_period_eq_lift_difference (γ * δ) θ hθ
  have hg := circlePathIntegerIncrement_mul_period_eq_lift_difference γ
    (circlePathArgumentLift γ) (circlePathArgumentLift_projects γ)
  have hd := circlePathIntegerIncrement_mul_period_eq_lift_difference δ
    (circlePathArgumentLift δ) (circlePathArgumentLift_projects δ)
  have h0 := circleProductArgumentCarry_formula (γ 0) (δ 0)
  have h1 := circleProductArgumentCarry_formula (γ 1) (δ 1)
  change (circlePathIntegerIncrement (γ * δ) : ℝ) * (2 * Real.pi) =
    (circlePathArgumentLift γ 1 + circlePathArgumentLift δ 1) -
      (circlePathArgumentLift γ 0 + circlePathArgumentLift δ 0) +
      Complex.arg (γ 0 * δ 0) - Complex.arg (γ 1 * δ 1) at h
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_add, Int.cast_sub]
  apply mul_right_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)
  linarith

end ChenRanks
