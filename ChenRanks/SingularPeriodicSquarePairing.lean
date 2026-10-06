import ChenRanks.SingularPeriodicSquareCycle
import ChenRanks.SingularClosedPathEvaluation

/-!
# Genuine cohomology pairing on the original periodic square

Both loops are the actual coordinate edges of the same original map.
Their true periodic endpoints give genuine singular one-cycles. The
actual native cup pairing on the original two-cycle is their determinant,
for arbitrary native first-cohomology classes, without selected
representatives as an additional hypothesis.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

/-- The actual bottom coordinate path of the original square. -/
def periodicSquareHorizontalPath (F : C(I × I, X)) : C(I, X) :=
  F.comp ((ContinuousMap.id I).prodMk (ContinuousMap.const I 0))

/-- The actual left coordinate path of the original square. -/
def periodicSquareVerticalPath (F : C(I × I, X)) : C(I, X) :=
  F.comp ((ContinuousMap.const I 0).prodMk (ContinuousMap.id I))

theorem periodicSquareHorizontalPath_endpoints (F : C(I × I, X))
    (hv : ∀ t, F (1, t) = F (0, t)) :
    periodicSquareHorizontalPath X F 0 = periodicSquareHorizontalPath X F 1 :=
  (hv 0).symm

theorem periodicSquareVerticalPath_endpoints (F : C(I × I, X))
    (hh : ∀ t, F (t, 0) = F (t, 1)) :
    periodicSquareVerticalPath X F 0 = periodicSquareVerticalPath X F 1 := hh 0

theorem square_horizontal_edge_eq_simplexOfPath (F : C(I × I, X)) :
    edge X 2 (squarePositiveSimplex X F) =
      simplexOfPath X (periodicSquareHorizontalPath X F) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_simplexOfPath]
  ext t
  rw [geometricSimplexPath_edge]
  change geometricSimplex X 2 (squarePositiveSimplex X F) (realTriangleFacePath 2 t) = F (t, 0)
  rw [geometricSimplex_squarePositiveSimplex, realSquarePositiveTriangle_face]
  rfl

theorem square_vertical_edge_eq_simplexOfPath (F : C(I × I, X)) :
    edge X 2 (squareNegativeSimplex X F) =
      simplexOfPath X (periodicSquareVerticalPath X F) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_simplexOfPath]
  ext t
  rw [geometricSimplexPath_edge]
  change geometricSimplex X 2 (squareNegativeSimplex X F) (realTriangleFacePath 2 t) = F (0, t)
  rw [geometricSimplex_squareNegativeSimplex, realSquareNegativeTriangle_face]
  rfl

variable (k : Type) [Field k]

/-- The original cup-product pairing is the determinant of the two original loop pairings. -/
theorem cycleEvaluation_cup_periodicSquare_eq_loop_determinant
    (F : C(I × I, X)) (hv : ∀ t, F (1, t) = F (0, t))
    (hh : ∀ t, F (t, 0) = F (t, 1)) (a b : cohomology k X 1) :
    cycleEvaluation k X 1 (periodicSquareChain X k F)
        (boundary_periodicSquareChain_eq_zero X k F hv hh) (cup k X a b) =
      closedPathEvaluation k X (periodicSquareHorizontalPath X F)
          (periodicSquareHorizontalPath_endpoints X F hv) a *
        closedPathEvaluation k X (periodicSquareVerticalPath X F)
          (periodicSquareVerticalPath_endpoints X F hh) b -
      closedPathEvaluation k X (periodicSquareVerticalPath X F)
          (periodicSquareVerticalPath_endpoints X F hh) a *
        closedPathEvaluation k X (periodicSquareHorizontalPath X F)
          (periodicSquareHorizontalPath_endpoints X F hv) b := by
  obtain ⟨a', rfl⟩ := cocycleClass_surjective k X 1 a
  obtain ⟨b', rfl⟩ := cocycleClass_surjective k X 1 b
  rw [cycleEvaluation_cup_periodicSquare X k F hv hh, square_horizontal_edge_eq_simplexOfPath,
    square_vertical_edge_eq_simplexOfPath]
  simp only [closedPathEvaluation_cocycleClass]

end ChenRanks.SingularCohomology
