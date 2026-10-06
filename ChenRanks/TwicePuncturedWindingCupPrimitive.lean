import ChenRanks.TwicePuncturedTriangleClosingWinding
import ChenRanks.ArrangementBoundaryCupPullbacks

/-!
# An explicit original singular primitive of the winding cup

On an original one-simplex, take minus the genuine finite total winding
of its genuine phase-grid closing loop. The genuine triangle formula
computes its differential as the actual Alexander--Whitney product of
the original z and 1-z winding cochains. Consequently their cup vanishes
in the original native singular cohomology. No vanishing theorem,
cohomology dimension or cochain differential identity is an input.
-/

noncomputable section

open AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks

variable (k : Type) [Field k]

def twicePuncturedClosingWindingCochain : cochains k TwicePuncturedComplex 1 :=
  ofValues k TwicePuncturedComplex 1
    (fun s => -(twicePuncturedPathClosingWinding
      (geometricSimplexPath TwicePuncturedComplex s) : k))

theorem values_twicePuncturedClosingWindingCochain
    (s : simplices TwicePuncturedComplex 1) :
    values k TwicePuncturedComplex 1 (twicePuncturedClosingWindingCochain k) s =
      -(twicePuncturedPathClosingWinding
        (geometricSimplexPath TwicePuncturedComplex s) : k) :=
  congrFun (values_ofValues k TwicePuncturedComplex 1 _) s

theorem differential_twicePuncturedClosingWindingCochain :
    differential k TwicePuncturedComplex 1 (twicePuncturedClosingWindingCochain k) =
      cupOne k TwicePuncturedComplex
        (cochainPullback k twicePuncturedComplexZeroPhase 1 (circleWindingCochain k))
        (cochainPullback k twicePuncturedComplexOnePhase 1 (circleWindingCochain k)) := by
  apply cochain_ext k TwicePuncturedComplex 2
  intro s
  change values k TwicePuncturedComplex 2
      (differential k TwicePuncturedComplex 1 (twicePuncturedClosingWindingCochain k)) s =
    values k TwicePuncturedComplex 2
      (cupOne k TwicePuncturedComplex
        (cochainPullback k twicePuncturedComplexZeroPhase 1 (circleWindingCochain k))
        (cochainPullback k twicePuncturedComplexOnePhase 1 (circleWindingCochain k))) s
  rw [values_differential_one, values_twicePuncturedClosingWindingCochain,
    values_twicePuncturedClosingWindingCochain, values_twicePuncturedClosingWindingCochain,
    values_cupOne, values_cochainPullback, values_cochainPullback,
    values_circleWindingCochain, values_circleWindingCochain]
  simp only [circleWindingValue, geometricSimplexPath_simplexMap, geometricSimplexPath_edge]
  have h := congrArg (fun z : ℤ => (z : k))
    (twicePuncturedPathClosingWinding_realTriangle
      (geometricSimplex TwicePuncturedComplex 2 s))
  simp only [Int.cast_add, Int.cast_mul] at h
  change
    -(twicePuncturedPathClosingWinding
      ((geometricSimplex TwicePuncturedComplex 2 s).comp (realTriangleFacePath 0)) : k) -
    -(twicePuncturedPathClosingWinding
      ((geometricSimplex TwicePuncturedComplex 2 s).comp (realTriangleFacePath 1)) : k) +
    -(twicePuncturedPathClosingWinding
      ((geometricSimplex TwicePuncturedComplex 2 s).comp (realTriangleFacePath 2)) : k) =
    ((twicePuncturedArgumentDeckIncrement
      ((geometricSimplex TwicePuncturedComplex 2 s).comp (realTriangleFacePath 2))).1 : k) *
    ((twicePuncturedArgumentDeckIncrement
      ((geometricSimplex TwicePuncturedComplex 2 s).comp (realTriangleFacePath 0))).2 : k)
  linear_combination h

theorem twicePuncturedWindingCup_eq_zero : twicePuncturedWindingCup = 0 := by
  rw [twicePuncturedWindingCup, twicePuncturedZeroWindingClass,
    twicePuncturedOneWindingClass, circleWindingClass,
    cohomologyPullback_cocycleClass, cohomologyPullback_cocycleClass, cup_cocycleClass]
  apply (cocycleClass_eq_zero_iff ℂ TwicePuncturedComplex 2 _).mpr
  apply (mem_positive_boundaries_iff ℂ TwicePuncturedComplex 1 _).mpr
  refine ⟨twicePuncturedClosingWindingCochain ℂ, ?_⟩
  rw [cocycleCochain_cocycleCup, cocycleCochain_cocyclePullback,
    cocycleCochain_cocyclePullback]
  exact differential_twicePuncturedClosingWindingCochain ℂ

end ChenRanks
