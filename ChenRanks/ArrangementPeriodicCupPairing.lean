import ChenRanks.SingularPeriodicSquarePairing
import ChenRanks.ArrangementWindingEvaluation

/-!
# Actual equation-class cup pairings on actual complement squares

This is the original complement's singular cup, paired with an actual
periodic square in that same complement. The entries are true integer
windings of the actual nonvanishing equations on its genuine coordinate
loops. No logarithmic/cup comparison, H¹ spanning, or rank formula is
included as an assumption or a conclusion.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open scoped BigOperators

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual cup of two actual equation classes has the true winding determinant. -/
theorem cycleEvaluation_equationCup_periodicSquare
    (F : C(I × I, A.Complement)) (hv : ∀ t, F (1, t) = F (0, t))
    (hh : ∀ t, F (t, 0) = F (t, 1)) (H K : ι) :
    cycleEvaluation ℂ A.Complement 1 (periodicSquareChain A.Complement ℂ F)
        (boundary_periodicSquareChain_eq_zero A.Complement ℂ F hv hh)
        (A.singularCup (A.equationWindingClass ℂ H) (A.equationWindingClass ℂ K)) =
      (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
          (periodicSquareHorizontalPath A.Complement F)) : ℂ) *
        (circlePathIntegerIncrement ((A.equationComplementCircleMap K).comp
          (periodicSquareVerticalPath A.Complement F)) : ℂ) -
      (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
          (periodicSquareVerticalPath A.Complement F)) : ℂ) *
        (circlePathIntegerIncrement ((A.equationComplementCircleMap K).comp
          (periodicSquareHorizontalPath A.Complement F)) : ℂ) := by
  rw [cycleEvaluation_cup_periodicSquare_eq_loop_determinant A.Complement ℂ F hv hh]
  simp only [closedPathEvaluation_equationWindingClass]

/-- The original coefficient map gives the determinant of its actual winding-weighted rows. -/
theorem cycleEvaluation_equationCoefficientCup_periodicSquare
    (F : C(I × I, A.Complement)) (hv : ∀ t, F (1, t) = F (0, t))
    (hh : ∀ t, F (t, 0) = F (t, 1)) (a b : ι → ℂ) :
    cycleEvaluation ℂ A.Complement 1 (periodicSquareChain A.Complement ℂ F)
        (boundary_periodicSquareChain_eq_zero A.Complement ℂ F hv hh)
        (A.singularCup (A.equationWindingClassMap a) (A.equationWindingClassMap b)) =
      (∑ H, a H • (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
          (periodicSquareHorizontalPath A.Complement F)) : ℂ)) *
        (∑ H, b H • (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
          (periodicSquareVerticalPath A.Complement F)) : ℂ)) -
      (∑ H, a H • (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
          (periodicSquareVerticalPath A.Complement F)) : ℂ)) *
        (∑ H, b H • (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp
          (periodicSquareHorizontalPath A.Complement F)) : ℂ)) := by
  rw [cycleEvaluation_cup_periodicSquare_eq_loop_determinant A.Complement ℂ F hv hh]
  simp only [closedPathEvaluation_equationWindingClassMap]

end ChenRanks.AffineArrangement
