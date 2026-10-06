import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic.Positivity

/-! Uncompiled preparation outside the active Lean sources.

The integer is extracted from an actual covering-space path lift and
the actual kernel of Circle.exp. It is not an assigned period label.
This file does not yet prove the singular triangle cocycle identity,
concatenation, or a comparison with original arrangement H¹. -/

noncomputable section

open unitInterval

namespace ChenRanks

/-- Lift an actual circle path from the actual real argument of its
initial point. The lift comes from the genuine covering map. -/
def circlePathArgumentLift (γ : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath γ (Complex.arg (γ 0))
    (Circle.exp_arg (γ 0)).symm

/-- Every point of the genuine path lift projects to the original path. -/
theorem circlePathArgumentLift_projects (γ : C(I, Circle)) (t : I) :
    Circle.exp (circlePathArgumentLift γ t) = γ t :=
  congrFun (Circle.isCoveringMap_exp.liftPath_lifts γ
    (Complex.arg (γ 0)) (Circle.exp_arg (γ 0)).symm) t

/-- Its initial value is the selected genuine argument. -/
theorem circlePathArgumentLift_zero (γ : C(I, Circle)) :
    circlePathArgumentLift γ 0 = Complex.arg (γ 0) :=
  Circle.isCoveringMap_exp.liftPath_zero γ (Complex.arg (γ 0))
    (Circle.exp_arg (γ 0)).symm

/-- The actual endpoint differs from the actual selected terminal
argument by one uniquely determined integer multiple of the period. -/
theorem circlePathIntegerIncrement_existsUnique (γ : C(I, Circle)) :
    ∃! n : ℤ, circlePathArgumentLift γ 1 =
      Complex.arg (γ 1) + (n : ℝ) * (2 * Real.pi) := by
  have he : Circle.exp (circlePathArgumentLift γ 1) =
      Circle.exp (Complex.arg (γ 1)) :=
    (circlePathArgumentLift_projects γ 1).trans (Circle.exp_arg (γ 1)).symm
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp he
  refine ⟨n, hn, ?_⟩
  intro m hm
  have hmn : (m : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) :=
    add_left_cancel (hm.symm.trans hn)
  exact Int.cast_injective (mul_right_cancel₀ (by positivity : 2 * Real.pi ≠ 0) hmn)

/-- The integer determined by the actual covering lift. -/
def circlePathIntegerIncrement (γ : C(I, Circle)) : ℤ :=
  (circlePathIntegerIncrement_existsUnique γ).exists.choose

/-- Its exact actual endpoint formula. -/
theorem circlePathIntegerIncrement_formula (γ : C(I, Circle)) :
    circlePathArgumentLift γ 1 = Complex.arg (γ 1) +
      (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi) :=
  (circlePathIntegerIncrement_existsUnique γ).exists.choose_spec

/-- An actual exponential path with actual endpoints 0 and n times
the period has integer increment n, by uniqueness of the true lift. -/
theorem circlePathIntegerIncrement_of_exp_path
    (θ : C(I, ℝ)) (n : ℤ) (h0 : θ 0 = 0)
    (h1 : θ 1 = (n : ℝ) * (2 * Real.pi)) :
    circlePathIntegerIncrement (Circle.exp.comp θ) = n := by
  let γ : C(I, Circle) := Circle.exp.comp θ
  have ha0 : Complex.arg (γ 0) = 0 := by
    simp only [γ, ContinuousMap.comp_apply, h0, Circle.exp_zero, Circle.coe_one,
      Complex.arg_one]
  have hlift : circlePathArgumentLift γ = θ := by
    apply Eq.symm
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr
    exact ⟨rfl, h0.trans ha0.symm⟩
  have hg1 : γ 1 = 1 := by
    simp only [γ, ContinuousMap.comp_apply, h1, Circle.exp_int_mul_two_pi]
  have ha1 : Complex.arg (γ 1) = 0 := by
    rw [hg1]
    exact Complex.arg_one
  have hw := circlePathIntegerIncrement_formula γ
  rw [hlift, h1, ha1, zero_add] at hw
  exact Int.cast_injective
    (mul_right_cancel₀ (by positivity : 2 * Real.pi ≠ 0) hw).symm

end ChenRanks
