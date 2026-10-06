import ChenRanks.SingularPeriodicSquareCycle

/-!
# Actual closed-path evaluation under a free loop homotopy

Two genuine ordered triangles fill the original square. The actual
cocycle equations and coinciding vertical edges prove that its bottom
and top paths have identical cocycle values. This retains endpoint
information that equality of cohomology pullbacks alone does not retain.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

def squareBottomPath (F : C(I × I, X)) : C(I, X) :=
  F.comp ⟨fun t => (t, 0), continuous_id.prodMk continuous_const⟩

def squareTopPath (F : C(I × I, X)) : C(I, X) :=
  F.comp ⟨fun t => (t, 1), continuous_id.prodMk continuous_const⟩

theorem simplexOfPath_squareBottomPath (F : C(I × I, X)) :
    simplexOfPath X (squareBottomPath X F) = edge X 2 (squarePositiveSimplex X F) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_simplexOfPath, geometricSimplexPath_edge]
  ext t
  change F (t, 0) = geometricSimplex X 2 (squarePositiveSimplex X F)
    (realTriangleFacePath 2 t)
  rw [geometricSimplex_squarePositiveSimplex, realSquarePositiveTriangle_face]
  simp

theorem simplexOfPath_squareTopPath (F : C(I × I, X)) :
    simplexOfPath X (squareTopPath X F) = edge X 0 (squareNegativeSimplex X F) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_simplexOfPath, geometricSimplexPath_edge]
  ext t
  change F (t, 1) = geometricSimplex X 2 (squareNegativeSimplex X F)
    (realTriangleFacePath 0 t)
  rw [geometricSimplex_squareNegativeSimplex, realSquareNegativeTriangle_face]
  simp

variable (k : Type) [Field k]

/-- Genuine free-loop edge equality and genuine cocycle closure imply
equal evaluation on the original bottom and top paths. -/
theorem closedCochain_values_squareBottom_eq_top (F : C(I × I, X))
    (hv : ∀ t, F (1, t) = F (0, t)) (a : cochains k X 1)
    (ha : differential k X 1 a = 0) :
    values k X 1 a (simplexOfPath X (squareBottomPath X F)) =
      values k X 1 a (simplexOfPath X (squareTopPath X F)) := by
  rw [simplexOfPath_squareBottomPath, simplexOfPath_squareTopPath]
  have hp := closedOne_triangle_relation k X a ha (squarePositiveSimplex X F)
  have hn := closedOne_triangle_relation k X a ha (squareNegativeSimplex X F)
  rw [square_diagonal_edges_eq X F, square_vertical_edges_eq X F hv] at hp
  linear_combination hn - hp

/-- The endpoint-sensitive identity descends to actual native H¹ evaluation. -/
theorem closedPathEvaluation_squareBottom_eq_top (F : C(I × I, X))
    (hv : ∀ t, F (1, t) = F (0, t)) (h : cohomology k X 1) :
    closedPathEvaluation k X (squareBottomPath X F) (hv 0).symm h =
      closedPathEvaluation k X (squareTopPath X F) (hv 1).symm h := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective k X 1 h
  rw [closedPathEvaluation_cocycleClass, closedPathEvaluation_cocycleClass]
  exact closedCochain_values_squareBottom_eq_top X k F hv
    (cocycleCochain k X 1 a) (cocycleCochain_closed k X 1 a)

end ChenRanks.SingularCohomology
