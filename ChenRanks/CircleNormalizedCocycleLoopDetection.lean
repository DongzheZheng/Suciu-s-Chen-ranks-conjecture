import ChenRanks.CircleNormalizedCocycleIntegerTurns
import ChenRanks.CirclePathIntegerIncrement
import ChenRanks.SingularSquareCocycleHomotopy

/-!
# Actual circle-loop detection from one actual positive generator

The genuine covering-space lift constructs a free homotopy from any
actual closed circle path to the actual integer-turn path. The lifted
endpoint difference is proved from the already constructed integer
increment, and makes the actual homotopy periodic. The native square
cocycle identity and the actual integer-turn calculation then prove
all-loop vanishing from one actual generator value. No generator or
cohomology classification theorem is assumed.
-/

noncomputable section

open unitInterval

namespace ChenRanks.SingularCohomology

/-- The actual covering-space endpoint formula for an actual closed path. -/
theorem circlePathArgumentLift_closed_endpoints (γ : C(I, Circle))
    (hclosed : γ 0 = γ 1) :
    circlePathArgumentLift γ 1 = circlePathArgumentLift γ 0 +
      (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi) := by
  have h := circlePathIntegerIncrement_formula γ
  rw [← hclosed, ← circlePathArgumentLift_zero γ] at h
  exact h

/-- The actual lift, with its chosen initial argument removed through
a genuine free homotopy, yields the actual signed integer-turn loop. -/
def circleLoopIntegerTurnsHomotopy (γ : C(I, Circle)) : C(I × I, Circle) :=
  Circle.exp.comp
    ⟨fun p => (1 - (p.2 : ℝ)) * circlePathArgumentLift γ p.1 +
      (p.2 : ℝ) * ((p.1 : ℝ) *
        ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi))), by fun_prop⟩

theorem circleLoopIntegerTurnsHomotopy_periodic (γ : C(I, Circle))
    (hclosed : γ 0 = γ 1) (s : I) :
    circleLoopIntegerTurnsHomotopy γ (1, s) =
      circleLoopIntegerTurnsHomotopy γ (0, s) := by
  change Circle.exp ((1 - (s : ℝ)) * circlePathArgumentLift γ 1 +
      (s : ℝ) * ((1 : ℝ) *
        ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)))) =
    Circle.exp ((1 - (s : ℝ)) * circlePathArgumentLift γ 0 +
      (s : ℝ) * ((0 : ℝ) *
        ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi))))
  rw [circlePathArgumentLift_closed_endpoints γ hclosed]
  rw [show (1 - (s : ℝ)) * (circlePathArgumentLift γ 0 +
        (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)) +
      (s : ℝ) * ((1 : ℝ) *
        ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi))) =
      ((1 - (s : ℝ)) * circlePathArgumentLift γ 0 +
        (s : ℝ) * ((0 : ℝ) *
          ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)))) +
        (circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi) from by ring]
  rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

theorem squareBottomPath_circleLoopIntegerTurnsHomotopy (γ : C(I, Circle)) :
    squareBottomPath Circle (circleLoopIntegerTurnsHomotopy γ) = γ := by
  apply ContinuousMap.ext
  intro t
  change Circle.exp ((1 - (0 : ℝ)) * circlePathArgumentLift γ t +
    (0 : ℝ) * ((t : ℝ) *
      ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)))) = γ t
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  exact circlePathArgumentLift_projects γ t

theorem squareTopPath_circleLoopIntegerTurnsHomotopy (γ : C(I, Circle)) :
    squareTopPath Circle (circleLoopIntegerTurnsHomotopy γ) =
      circleStraightPath 0 ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)) := by
  apply ContinuousMap.ext
  intro t
  change Circle.exp ((1 - (1 : ℝ)) * circlePathArgumentLift γ t +
      (1 : ℝ) * ((t : ℝ) *
        ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)))) =
    Circle.exp ((1 - (t : ℝ)) * 0 + (t : ℝ) *
      ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)))
  simp only [sub_self, zero_mul, one_mul, zero_add, mul_zero]

variable (k : Type) [Field k]

/-- A genuine closed circle cochain is detected on actual closed paths
by the one actual positive generator. -/
theorem circle_closedCochain_loop_value_eq_zero_of_generator
    (β : cochains k Circle 1) (hβ : differential k Circle 1 β = 0)
    (hgenerator : values k Circle 1 β
      (simplexOfPath Circle positiveUnitCircleTraversal) = 0)
    (γ : C(I, Circle)) (hclosed : γ 0 = γ 1) :
    values k Circle 1 β (simplexOfPath Circle γ) = 0 := by
  have h := closedCochain_values_squareBottom_eq_top Circle k
    (circleLoopIntegerTurnsHomotopy γ)
    (circleLoopIntegerTurnsHomotopy_periodic γ hclosed) β hβ
  rw [squareBottomPath_circleLoopIntegerTurnsHomotopy,
    squareTopPath_circleLoopIntegerTurnsHomotopy] at h
  have hgenerator' : circleStraightPathValue k β 0 (2 * Real.pi) = 0 := by
    unfold circleStraightPathValue
    rw [circleStraightPath_positive_generator]
    exact hgenerator
  change values k Circle 1 β (simplexOfPath Circle γ) =
    circleStraightPathValue k β 0
      ((circlePathIntegerIncrement γ : ℝ) * (2 * Real.pi)) at h
  exact h.trans (circleStraightPathValue_int_periods_eq_zero
    k β hβ hgenerator' (circlePathIntegerIncrement γ))

end ChenRanks.SingularCohomology
