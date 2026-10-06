import ChenRanks.BasedTwicePuncturedTriangleGridEdges
import ChenRanks.CircleTriangleIntegerIncrement
import ChenRanks.PhaseGridClosingWindingComparison
import ChenRanks.TwicePuncturedClosingWindingConcatenation

/-!
# The actual closing-winding relation on every original triangle

The genuinely based grid filling identifies its actual edge restrictions
with the selected lifts, including the necessary actual deck translation
of the second edge. At each genuine puncture the native winding cocycle
has its genuine triangle relation. The original triangle also proves the
same actual two-coordinate terminal integer. Thus its actual diagonal
and its actual concatenated boundary have equal actual closing tables.
The already proved closing concatenation then gives the precise cup
correction. No cochain coboundary or cup vanishing is an input.
-/

noncomputable section

open AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks

theorem twicePuncturedPathClosingWinding_triangle_concat
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    twicePuncturedPathClosingWinding
        (((triangleFirstEdgePath s).trans (triangleSecondEdgePath s)).toContinuousMap) =
      twicePuncturedPathClosingWinding (s.comp (realTriangleFacePath 1)) := by
  let p := triangleFirstEdgePath s
  let q := triangleSecondEdgePath s
  let γ := (p.trans q).toContinuousMap
  let δ := s.comp (realTriangleFacePath 1)
  have h0 : γ 0 = δ 0 := by
    change (p.trans q) 0 = s (realTriangleFacePath 1 0)
    rw [Path.source, realTriangleFacePath_zero]
    rfl
  have h1 : γ 1 = δ 1 := by
    change (p.trans q) 1 = s (realTriangleFacePath 1 1)
    rw [Path.target, realTriangleFacePath_one]
    rfl
  have hn : twicePuncturedArgumentDeckIncrement γ =
      twicePuncturedArgumentDeckIncrement δ := by
    rw [twicePuncturedArgumentDeckIncrement_native_trans]
    exact twicePuncturedArgumentDeckIncrement_realTriangle s
  apply twicePuncturedPathClosingWinding_eq_of_lift_increments γ δ h0 h1 hn
  intro i
  let G := basedTwicePuncturedSimplexGridLift 2 s
  let f : C(stdSimplex ℝ (Fin 3), Circle) := (phaseGridPointCircleMap i).comp G
  have hfirst : f.comp (realTriangleFacePath 2) =
      ((phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 2))).map
        (phaseGridPointCircleMap i).continuous).toContinuousMap := by
    change ((phaseGridPointCircleMap i).comp
      (basedTwicePuncturedSimplexGridLift 2 s)).comp (realTriangleFacePath 2) = _
    rw [ContinuousMap.comp_assoc, basedTwicePuncturedTriangle_first_edge_eq_selected]
    rfl
  have hsecond : f.comp (realTriangleFacePath 0) =
      (((phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 0))).map
        (phaseGridDeckTranslation
          (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2)))).continuous).map
            (phaseGridPointCircleMap i).continuous).toContinuousMap := by
    change ((phaseGridPointCircleMap i).comp
      (basedTwicePuncturedSimplexGridLift 2 s)).comp (realTriangleFacePath 0) = _
    rw [ContinuousMap.comp_assoc,
      basedTwicePuncturedTriangle_second_edge_eq_translated_selected]
    rfl
  have hdiagonal : f.comp (realTriangleFacePath 1) =
      ((phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 1))).map
        (phaseGridPointCircleMap i).continuous).toContinuousMap := by
    change ((phaseGridPointCircleMap i).comp
      (basedTwicePuncturedSimplexGridLift 2 s)).comp (realTriangleFacePath 1) = _
    rw [ContinuousMap.comp_assoc, basedTwicePuncturedTriangle_diagonal_edge_eq_selected]
    rfl
  have ht := circlePathIntegerIncrement_realTriangle f
  rw [hfirst, hsecond, hdiagonal] at ht
  change phaseGridPuncturePathIncrement i (phaseGridNativeLiftedPath (p.trans q)) = _
  rw [phaseGridNativeLiftedPath_trans, phaseGridPuncturePathIncrement_trans]
  exact ht

theorem twicePuncturedPathClosingWinding_realTriangle
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    twicePuncturedPathClosingWinding (s.comp (realTriangleFacePath 1)) =
      twicePuncturedPathClosingWinding (s.comp (realTriangleFacePath 2)) +
        twicePuncturedPathClosingWinding (s.comp (realTriangleFacePath 0)) +
        (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2))).1 *
          (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 0))).2 := by
  rw [← twicePuncturedPathClosingWinding_triangle_concat]
  exact twicePuncturedPathClosingWinding_native_trans
    (triangleFirstEdgePath s) (triangleSecondEdgePath s)

end ChenRanks
