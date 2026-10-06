import ChenRanks.ArrangementBoundaryWindingPullbacks
import ChenRanks.ArrangementEquationQuadraticCup

/-!
# Original boundary cups as actual twice-punctured-plane pullbacks

These identities are in native singular cohomology. They reduce the
actual parallel and triple boundary cups to the same actual cup class
on the actual twice-punctured plane. Its vanishing is a separate
cochain proof obligation, not a hypothesis of these identities.
-/

noncomputable section

namespace ChenRanks

open SingularCohomology

def twicePuncturedWindingCup : cohomology ℂ TwicePuncturedComplex 2 :=
  cup ℂ TwicePuncturedComplex
    (twicePuncturedZeroWindingClass ℂ) (twicePuncturedOneWindingClass ℂ)

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance boundaryCupPullbacksDecidableEq : DecidableEq ι := Classical.decEq ι

theorem equationWindingClassMap_single (H : ι) :
    A.equationWindingClassMap (Pi.single H 1) = A.equationWindingClass ℂ H := by
  classical
  simp [equationWindingClassMap, Pi.single_apply]

theorem parallelBoundaryCup_eq_actual_pullback
    (H K : ι) (hHK : H ≠ K) (c : ℂ) (hc : A.normal K = c • A.normal H) :
    A.equationQuadraticCup
        (exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)) =
      cohomologyPullback ℂ (A.parallelBoundaryCurveMap H K hHK c hc) 2
        twicePuncturedWindingCup := by
  rw [twicePuncturedWindingCup, cohomologyPullback_cup,
    parallelBoundaryCurveMap_zero_winding_pullback ℂ A H K hHK c hc,
    parallelBoundaryCurveMap_one_winding_pullback ℂ A H K hHK c hc,
    A.equationQuadraticCup_exteriorWedge,
    A.equationWindingClassMap_single, A.equationWindingClassMap_single]

theorem tripleBoundaryCup_eq_neg_actual_pullback
    (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L) (a b : ℂ)
    (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    A.equationQuadraticCup (tripleBoundary H K L) =
      -cohomologyPullback ℂ (A.tripleBoundaryCurveMap H K L hHL hKL a b h) 2
        twicePuncturedWindingCup := by
  rw [twicePuncturedWindingCup, cohomologyPullback_cup,
    tripleBoundaryCurveMap_zero_winding_pullback ℂ A H K L hHL hKL a b h,
    tripleBoundaryCurveMap_one_winding_pullback ℂ A H K L hHL hKL a b h]
  simp only [tripleBoundary, map_add, map_sub,
    A.equationQuadraticCup_exteriorWedge, A.equationWindingClassMap_single]
  simp only [singularCup, LinearMap.sub_apply, cup_self_eq_zero]
  abel

end AffineArrangement

end ChenRanks
