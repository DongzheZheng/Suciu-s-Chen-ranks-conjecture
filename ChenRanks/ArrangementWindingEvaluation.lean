import ChenRanks.ArrangementSingularWindingClasses
import ChenRanks.SingularPathFunctoriality
import ChenRanks.CircleClosedPathEvaluation

/-!
# Exact evaluation of actual equation classes on actual complement loops

These formulas identify the genuine equation-class pairing with true
integer increments of the actual circle-valued equation paths. The
coefficient-space formula is derived from the native linear cohomology
evaluation. No meridian basis or cohomology dimension is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open scoped BigOperators

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual equation class is evaluated by the true winding of the actual image path. -/
theorem closedPathEvaluation_equationWindingClass (k : Type) [Field k]
    (H : ι) (γ : C(I, A.Complement)) (hγ : γ 0 = γ 1) :
    closedPathEvaluation k A.Complement γ hγ (A.equationWindingClass k H) =
      (circlePathIntegerIncrement ((A.equationComplementCircleMap H).comp γ) : k) := by
  rw [equationWindingClass, closedPathEvaluation_cohomologyPullback,
    closedPathEvaluation_circleWindingClass_eq_increment]

/-- The genuine original coefficient map has the genuine loop-pairing formula. -/
theorem closedPathEvaluation_equationWindingClassMap
    (γ : C(I, A.Complement)) (hγ : γ 0 = γ 1) (a : ι → ℂ) :
    closedPathEvaluation ℂ A.Complement γ hγ (A.equationWindingClassMap a) =
      ∑ H, a H • (circlePathIntegerIncrement
        ((A.equationComplementCircleMap H).comp γ) : ℂ) := by
  change closedPathEvaluation ℂ A.Complement γ hγ
    (∑ H, a H • A.equationWindingClass ℂ H) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro H _
  rw [map_smul, closedPathEvaluation_equationWindingClass]

end ChenRanks.AffineArrangement
