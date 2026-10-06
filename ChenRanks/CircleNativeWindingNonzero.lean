import ChenRanks.CircleSingularWindingCocycle
import ChenRanks.SingularClosedPathEvaluation

/-!
# Nonvanishing of the true circle winding class

The original exponential circle loop gives an actual singular cycle.
Its native winding cocycle has value one, so its original singular
cohomology class is nonzero. This does not assert that the class spans
all of first cohomology.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

/-- The actual linear real path going once through the circle period. -/
def circleSingleTurnArgumentPath : C(I, ℝ) :=
  ⟨fun t => (t : ℝ) * (2 * Real.pi), continuous_subtype_val.mul continuous_const⟩

/-- The original exponential circle loop. -/
def circleSingleTurnPath : C(I, Circle) := Circle.exp.comp circleSingleTurnArgumentPath

theorem circleSingleTurnPath_closed : circleSingleTurnPath 0 = circleSingleTurnPath 1 := by
  simp [circleSingleTurnPath, circleSingleTurnArgumentPath]

/-- The integer is computed by the actual lift of this actual loop. -/
theorem circleWindingValue_singleTurn :
    circleWindingValue (simplexOfPath Circle circleSingleTurnPath) = 1 := by
  rw [circleWindingValue, geometricSimplexPath_simplexOfPath]
  exact circlePathIntegerIncrement_of_exp_path circleSingleTurnArgumentPath 1
    (by simp [circleSingleTurnArgumentPath]) (by simp [circleSingleTurnArgumentPath])

variable (k : Type) [Field k]

/-- Native cohomology evaluation is one on the actual winding class. -/
theorem closedPathEvaluation_circleWindingClass :
    closedPathEvaluation k Circle circleSingleTurnPath circleSingleTurnPath_closed
      (circleWindingClass k) = 1 := by
  rw [circleWindingClass, closedPathEvaluation_cocycleClass]
  change values k Circle 1 (circleWindingCochain k)
    (simplexOfPath Circle circleSingleTurnPath) = 1
  rw [values_circleWindingCochain, circleWindingValue_singleTurn, Int.cast_one]

/-- The actual singular winding class is nonzero over every coefficient field. -/
theorem circleWindingClass_ne_zero : circleWindingClass k ≠ 0 := by
  intro h
  have he := closedPathEvaluation_circleWindingClass k
  rw [h, map_zero] at he
  exact zero_ne_one he

end ChenRanks.SingularCohomology
