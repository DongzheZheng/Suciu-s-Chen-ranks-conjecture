import ChenRanks.CirclePathIntegerIncrement
import Mathlib.Tactic.Linarith

/-!
# Integer increments from actual lifted endpoint differences

Any genuine real lift of the same original circle path gives the same
integer increment, after the selected endpoint arguments are accounted
for. The formula supplies the telescoping identity needed when the three
edges of a singular triangle come from one real lift of that triangle.
Existence of the triangle lift and identification with native singular
face maps remain separate constructions.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The actual integer increment is computed from any genuine real lift,
independently of the starting value of that lift. -/
theorem circlePathIntegerIncrement_mul_period_eq_lift_difference
    (γ : C(I, Circle)) (θ : C(I, ℝ))
    (hθ : ∀ t, Circle.exp (θ t) = γ t) :
    (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi) =
      θ 1 - θ 0 + Complex.arg (γ 0) - Complex.arg (γ 1) := by
  let Θ : C(I, ℝ) :=
    ⟨fun t => θ t - θ 0 + Complex.arg (γ 0), by fun_prop⟩
  have hΘ : Circle.exp ∘ Θ = γ := by
    funext t
    change Circle.exp (θ t - θ 0 + Complex.arg (γ 0)) = γ t
    rw [Circle.exp_add, Circle.exp_sub, hθ t, hθ 0, Circle.exp_arg]
    simp
  have hzero : Θ 0 = Complex.arg (γ 0) := by
    change θ 0 - θ 0 + Complex.arg (γ 0) = _
    rw [sub_self, zero_add]
  have hlift : Θ = circlePathArgumentLift γ :=
    (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨hΘ, hzero⟩
  have h := circlePathIntegerIncrement_formula γ
  rw [← hlift] at h
  change θ 1 - θ 0 + Complex.arg (γ 0) =
    Complex.arg (γ 1) + (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi) at h
  linarith

/-- Three original circle paths arising from one set of lifted vertex
values have the genuine integer cocycle relation, including the selected
argument terms. The geometric singular triangle supplies these endpoints. -/
theorem circlePathIntegerIncrement_triangle_of_lifted_endpoints
    (γ01 γ12 γ02 : C(I, Circle)) (θ01 θ12 θ02 : C(I, ℝ))
    (h01 : ∀ t, Circle.exp (θ01 t) = γ01 t)
    (h12 : ∀ t, Circle.exp (θ12 t) = γ12 t)
    (h02 : ∀ t, Circle.exp (θ02 t) = γ02 t)
    (h0 : θ01 0 = θ02 0) (h1 : θ01 1 = θ12 0)
    (h2 : θ12 1 = θ02 1) :
    circlePathIntegerIncrement γ01 + circlePathIntegerIncrement γ12 =
      circlePathIntegerIncrement γ02 := by
  have g0 : γ01 0 = γ02 0 := (h01 0).symm.trans
    ((congrArg Circle.exp h0).trans (h02 0))
  have g1 : γ01 1 = γ12 0 := (h01 1).symm.trans
    ((congrArg Circle.exp h1).trans (h12 0))
  have g2 : γ12 1 = γ02 1 := (h12 1).symm.trans
    ((congrArg Circle.exp h2).trans (h02 1))
  have a := circlePathIntegerIncrement_mul_period_eq_lift_difference γ01 θ01 h01
  have b := circlePathIntegerIncrement_mul_period_eq_lift_difference γ12 θ12 h12
  have c := circlePathIntegerIncrement_mul_period_eq_lift_difference γ02 θ02 h02
  rw [h0, h1, g0, g1] at a
  rw [h2, g2] at b
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add]
  apply mul_right_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)
  linarith

end ChenRanks
