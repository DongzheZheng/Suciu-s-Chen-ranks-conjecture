import ChenRanks.ArrangementPointMeridianWinding
import ChenRanks.ArrangementPeriodicCupPairing

/-!
# Exact native cup pairing on the constructed original localized square

The actual original incidence and actual original meridian integers
are proved before evaluating the genuine native singular two-cycle.
The resulting augmentation determinant is a theorem about the original
complement's actual cup, not a prescribed combinatorial pairing.
-/

noncomputable section
open CategoryTheory AlgebraicTopology unitInterval
open scoped BigOperators
namespace ChenRanks.AffineArrangement
open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- The original incidence coefficient sum at the original affine point. -/
def pointIncidentCoefficientSum (x : Fin d → ℂ) (a : ι → ℂ) : ℂ :=
  ∑ K, if A.normal K x = A.offset K then a K else 0

/-- The actual cup pairing on a genuinely constructed original localized cycle
is the actual incidence/meridian augmentation determinant. -/
theorem actualPointMeridianSquare_coefficientCup
    (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) (a b : ι → ℂ) :
    cycleEvaluation ℂ A.Complement 1
        (periodicSquareChain A.Complement ℂ (A.actualPointMeridianSquare x H))
        (A.boundary_actualPointMeridianSquare_eq_zero x H)
        (A.singularCup (A.equationWindingClassMap a) (A.equationWindingClassMap b)) =
      A.pointIncidentCoefficientSum x a * b H.val -
        a H.val * A.pointIncidentCoefficientSum x b := by
  rw [A.cycleEvaluation_equationCoefficientCup_periodicSquare
    (A.actualPointMeridianSquare x H)
    (A.actualPointMeridianSquare_vertical_periodic x H)
    (A.actualPointMeridianSquare_horizontal_periodic x H)]
  simp [pointIncidentCoefficientSum, A.actualPointMeridianSquare_horizontal_increment,
    A.actualPointMeridianSquare_vertical_increment, smul_eq_mul]

end ChenRanks.AffineArrangement
