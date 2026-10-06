import ChenRanks.ArrangementBoundaryCurveMaps
import ChenRanks.NonzeroComplexWindingClassOperations
import ChenRanks.SingularPullbackComposition
import ChenRanks.ArrangementSingularWindingClasses

/-!
# Actual winding classes of the affine boundary maps

The two classes on the actual twice-punctured plane pull back to the
original equation classes, or their actual differences. The original
affine offsets and polynomial relations supply the maps and their
nonvanishing functions. No cup vanishing or cohomology comparison is
assumed here.
-/

noncomputable section

namespace ChenRanks

open SingularCohomology

variable (k : Type) [Field k]

def twicePuncturedZeroWindingClass : cohomology k TwicePuncturedComplex 1 :=
  cohomologyPullback k twicePuncturedComplexZeroPhase 1 (circleWindingClass k)

def twicePuncturedOneWindingClass : cohomology k TwicePuncturedComplex 1 :=
  cohomologyPullback k twicePuncturedComplexOnePhase 1 (circleWindingClass k)

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem parallelBoundaryCurveMap_zero_winding_pullback
    (H K : ι) (hHK : H ≠ K) (c : ℂ) (hc : A.normal K = c • A.normal H) :
    cohomologyPullback k (A.parallelBoundaryCurveMap H K hHK c hc) 1
        (twicePuncturedZeroWindingClass k) = A.equationWindingClass k H := by
  rw [twicePuncturedZeroWindingClass, cohomologyPullback_comp_apply]
  change cohomologyPullback k
    ((nonzeroComplexCircleMap.comp twicePuncturedComplexZeroMap).comp
      (A.parallelBoundaryCurveMap H K hHK c hc)) 1 (circleWindingClass k) = _
  rw [ContinuousMap.comp_assoc, A.parallelBoundaryCurveMap_zero_factor,
    cohomologyPullback_nonzero_winding_scale]
  rfl

theorem parallelBoundaryCurveMap_one_winding_pullback
    (H K : ι) (hHK : H ≠ K) (c : ℂ) (hc : A.normal K = c • A.normal H) :
    cohomologyPullback k (A.parallelBoundaryCurveMap H K hHK c hc) 1
        (twicePuncturedOneWindingClass k) = A.equationWindingClass k K := by
  rw [twicePuncturedOneWindingClass, cohomologyPullback_comp_apply]
  change cohomologyPullback k
    ((nonzeroComplexCircleMap.comp twicePuncturedComplexOneMap).comp
      (A.parallelBoundaryCurveMap H K hHK c hc)) 1 (circleWindingClass k) = _
  rw [ContinuousMap.comp_assoc, A.parallelBoundaryCurveMap_one_factor,
    cohomologyPullback_nonzero_winding_scale]
  rfl

theorem tripleBoundaryCurveMap_zero_winding_pullback
    (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L) (a b : ℂ)
    (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    cohomologyPullback k (A.tripleBoundaryCurveMap H K L hHL hKL a b h) 1
        (twicePuncturedZeroWindingClass k) =
      A.equationWindingClass k H - A.equationWindingClass k K := by
  rw [twicePuncturedZeroWindingClass, cohomologyPullback_comp_apply]
  change cohomologyPullback k
    ((nonzeroComplexCircleMap.comp twicePuncturedComplexZeroMap).comp
      (A.tripleBoundaryCurveMap H K L hHL hKL a b h)) 1 (circleWindingClass k) = _
  rw [ContinuousMap.comp_assoc, A.tripleBoundaryCurveMap_zero_factor,
    cohomologyPullback_nonzero_winding_scale, cohomologyPullback_nonzero_winding_quotient]
  rfl

theorem tripleBoundaryCurveMap_one_winding_pullback
    (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L) (a b : ℂ)
    (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    cohomologyPullback k (A.tripleBoundaryCurveMap H K L hHL hKL a b h) 1
        (twicePuncturedOneWindingClass k) =
      A.equationWindingClass k L - A.equationWindingClass k K := by
  rw [twicePuncturedOneWindingClass, cohomologyPullback_comp_apply]
  change cohomologyPullback k
    ((nonzeroComplexCircleMap.comp twicePuncturedComplexOneMap).comp
      (A.tripleBoundaryCurveMap H K L hHL hKL a b h)) 1 (circleWindingClass k) = _
  rw [ContinuousMap.comp_assoc, A.tripleBoundaryCurveMap_one_factor,
    cohomologyPullback_nonzero_winding_scale, cohomologyPullback_nonzero_winding_quotient]
  rfl

end AffineArrangement

end ChenRanks
