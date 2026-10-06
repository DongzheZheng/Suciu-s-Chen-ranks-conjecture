import ChenRanks.CircleSingularWindingCocycle
import ChenRanks.PhaseGridClosingPaths

/-!
# Actual integer increments along the original triangle edges

The real lift of the actual circle-valued triangle restricts to its
actual three faces. Its endpoint differences telescope. This supplies
the literal continuous-map edge identity and the actual two-coordinate
deck-increment identity without any assigned triangle data.
-/

noncomputable section

open AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks

theorem circlePathIntegerIncrement_realTriangle
    (s : C(stdSimplex ℝ (Fin 3), Circle)) :
    circlePathIntegerIncrement (s.comp (realTriangleFacePath 2)) +
      circlePathIntegerIncrement (s.comp (realTriangleFacePath 0)) =
        circlePathIntegerIncrement (s.comp (realTriangleFacePath 1)) := by
  let F := circleSimplexArgumentLift 2 s
  let θ : Fin 3 → C(I, ℝ) := fun i => F.comp (realTriangleFacePath i)
  have hθ (i : Fin 3) (t : I) :
      Circle.exp (θ i t) = (s.comp (realTriangleFacePath i)) t :=
    circleSimplexArgumentLift_projects 2 s (realTriangleFacePath i t)
  have h0 : θ 2 0 = θ 1 0 := by
    change F (realTriangleFacePath 2 0) = F (realTriangleFacePath 1 0)
    rw [realTriangleFacePath_zero, realTriangleFacePath_zero]
    rfl
  have h1 : θ 2 1 = θ 0 0 := by
    change F (realTriangleFacePath 2 1) = F (realTriangleFacePath 0 0)
    rw [realTriangleFacePath_one, realTriangleFacePath_zero]
    rfl
  have h2 : θ 0 1 = θ 1 1 := by
    change F (realTriangleFacePath 0 1) = F (realTriangleFacePath 1 1)
    rw [realTriangleFacePath_one, realTriangleFacePath_one]
    rfl
  exact circlePathIntegerIncrement_triangle_of_lifted_endpoints _ _ _
    (θ 2) (θ 0) (θ 1) (hθ 2) (hθ 0) (hθ 1) h0 h1 h2

theorem twicePuncturedArgumentDeckIncrement_realTriangle
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2)) +
      twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 0)) =
        twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 1)) := by
  apply Prod.ext
  · simpa only [twicePuncturedArgumentDeckIncrement, Prod.fst_add,
      ContinuousMap.comp_assoc] using
      circlePathIntegerIncrement_realTriangle (twicePuncturedComplexZeroPhase.comp s)
  · simpa only [twicePuncturedArgumentDeckIncrement, Prod.snd_add,
      ContinuousMap.comp_assoc] using
      circlePathIntegerIncrement_realTriangle (twicePuncturedComplexOnePhase.comp s)

end ChenRanks
