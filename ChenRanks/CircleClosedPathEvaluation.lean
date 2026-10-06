import ChenRanks.CircleNativeWindingNonzero

/-! Actual cohomological evaluation of the winding class on every original closed circle path. -/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k]

/-- Actual native cohomology evaluation gives the actual integer from the covering lift. -/
theorem closedPathEvaluation_circleWindingClass_eq_increment
    (γ : C(I, Circle)) (hγ : γ 0 = γ 1) :
    closedPathEvaluation k Circle γ hγ (circleWindingClass k) =
      (circlePathIntegerIncrement γ : k) := by
  rw [circleWindingClass, closedPathEvaluation_cocycleClass]
  change values k Circle 1 (circleWindingCochain k) (simplexOfPath Circle γ) = _
  rw [values_circleWindingCochain]
  change (circlePathIntegerIncrement (geometricSimplexPath Circle (simplexOfPath Circle γ)) : k) = _
  rw [geometricSimplexPath_simplexOfPath]

end ChenRanks.SingularCohomology
