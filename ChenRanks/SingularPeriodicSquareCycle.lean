import ChenRanks.SingularSquareTriangleGeometry
import ChenRanks.SingularPathFunctoriality
import ChenRanks.SingularCycleEvaluation

/-!
# Genuine singular two-cycles from actual periodic squares

The original continuous square is cut into two actual ordered singular
triangles. Actual periodic edge identities make their original singular
boundaries cancel. The Alexander--Whitney product on this genuine cycle
is the determinant of the genuine horizontal and vertical edge values.
No cycle label, boundary identity, or cup pairing is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

/-- The original positive singular triangle cut from the actual square. -/
def squarePositiveSimplex (F : C(I × I, X)) : simplices X 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk 2))).symm
    (F.comp realSquarePositiveTriangle)

/-- The original negative singular triangle cut from the same actual square. -/
def squareNegativeSimplex (F : C(I × I, X)) : simplices X 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk 2))).symm
    (F.comp realSquareNegativeTriangle)

theorem geometricSimplex_squarePositiveSimplex (F : C(I × I, X))
    (x : stdSimplex ℝ (Fin 3)) :
    geometricSimplex X 2 (squarePositiveSimplex X F) x = F (realSquarePositiveTriangle x) :=
  DFunLike.congr_fun ((TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply
      (F.comp realSquarePositiveTriangle)) x

theorem geometricSimplex_squareNegativeSimplex (F : C(I × I, X))
    (x : stdSimplex ℝ (Fin 3)) :
    geometricSimplex X 2 (squareNegativeSimplex X F) x = F (realSquareNegativeTriangle x) :=
  DFunLike.congr_fun ((TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply
      (F.comp realSquareNegativeTriangle)) x

/-- Both original diagonal simplices coincide, including their actual parametrizations. -/
theorem square_diagonal_edges_eq (F : C(I × I, X)) :
    edge X 1 (squarePositiveSimplex X F) = edge X 1 (squareNegativeSimplex X F) := by
  apply geometricSimplexPath_injective
  ext t
  rw [geometricSimplexPath_edge, geometricSimplexPath_edge]
  change geometricSimplex X 2 (squarePositiveSimplex X F) (realTriangleFacePath 1 t) =
    geometricSimplex X 2 (squareNegativeSimplex X F) (realTriangleFacePath 1 t)
  rw [geometricSimplex_squarePositiveSimplex, geometricSimplex_squareNegativeSimplex,
    realSquarePositiveTriangle_face, realSquareNegativeTriangle_face]
  simp

/-- Actual left/right periodicity identifies the true vertical singular edges. -/
theorem square_vertical_edges_eq (F : C(I × I, X)) (hv : ∀ t, F (1, t) = F (0, t)) :
    edge X 0 (squarePositiveSimplex X F) = edge X 2 (squareNegativeSimplex X F) := by
  apply geometricSimplexPath_injective
  ext t
  rw [geometricSimplexPath_edge, geometricSimplexPath_edge]
  change geometricSimplex X 2 (squarePositiveSimplex X F) (realTriangleFacePath 0 t) =
    geometricSimplex X 2 (squareNegativeSimplex X F) (realTriangleFacePath 2 t)
  rw [geometricSimplex_squarePositiveSimplex, geometricSimplex_squareNegativeSimplex,
    realSquarePositiveTriangle_face, realSquareNegativeTriangle_face]
  simpa using hv t

/-- Actual bottom/top periodicity identifies the true horizontal singular edges. -/
theorem square_horizontal_edges_eq (F : C(I × I, X)) (hh : ∀ t, F (t, 0) = F (t, 1)) :
    edge X 2 (squarePositiveSimplex X F) = edge X 0 (squareNegativeSimplex X F) := by
  apply geometricSimplexPath_injective
  ext t
  rw [geometricSimplexPath_edge, geometricSimplexPath_edge]
  change geometricSimplex X 2 (squarePositiveSimplex X F) (realTriangleFacePath 2 t) =
    geometricSimplex X 2 (squareNegativeSimplex X F) (realTriangleFacePath 0 t)
  rw [geometricSimplex_squarePositiveSimplex, geometricSimplex_squareNegativeSimplex,
    realSquarePositiveTriangle_face, realSquareNegativeTriangle_face]
  simpa using hh t

variable (k : Type) [Field k]

/-- The actual difference of the original two native singular triangle chains. -/
def periodicSquareChain (F : C(I × I, X)) : (chains k X).X 2 :=
  simplexChain k X 2 (squarePositiveSimplex X F) -
    simplexChain k X 2 (squareNegativeSimplex X F)

/-- Its original native singular boundary is zero by the true periodic face equalities. -/
theorem boundary_periodicSquareChain_eq_zero (F : C(I × I, X))
    (hv : ∀ t, F (1, t) = F (0, t)) (hh : ∀ t, F (t, 0) = F (t, 1)) :
    ((chains k X).d 2 1).hom (periodicSquareChain X k F) = 0 := by
  rw [periodicSquareChain, map_sub, boundary_simplexChain, boundary_simplexChain]
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    zero_add, add_zero, pow_zero, pow_one, pow_succ, mul_neg, mul_one,
    neg_neg, one_zsmul, neg_one_zsmul]
  change (simplexChain k X 1 (edge X 0 (squarePositiveSimplex X F)) +
      (-simplexChain k X 1 (edge X 1 (squarePositiveSimplex X F)) +
      simplexChain k X 1 (edge X 2 (squarePositiveSimplex X F)))) -
    (simplexChain k X 1 (edge X 0 (squareNegativeSimplex X F)) +
      (-simplexChain k X 1 (edge X 1 (squareNegativeSimplex X F)) +
      simplexChain k X 1 (edge X 2 (squareNegativeSimplex X F)))) = 0
  rw [square_diagonal_edges_eq X F, square_vertical_edges_eq X F hv,
    ← square_horizontal_edges_eq X F hh]
  abel

/-- The true original AW cup value is the true edge-value determinant. -/
theorem cupOne_periodicSquareChain (F : C(I × I, X))
    (hv : ∀ t, F (1, t) = F (0, t)) (hh : ∀ t, F (t, 0) = F (t, 1))
    (a b : cochains k X 1) :
    cupOne k X a b (periodicSquareChain X k F) =
      values k X 1 a (edge X 2 (squarePositiveSimplex X F)) *
        values k X 1 b (edge X 2 (squareNegativeSimplex X F)) -
      values k X 1 a (edge X 2 (squareNegativeSimplex X F)) *
        values k X 1 b (edge X 2 (squarePositiveSimplex X F)) := by
  rw [periodicSquareChain, map_sub]
  change values k X 2 (cupOne k X a b) (squarePositiveSimplex X F) -
    values k X 2 (cupOne k X a b) (squareNegativeSimplex X F) = _
  rw [values_cupOne, values_cupOne, square_vertical_edges_eq X F hv,
    ← square_horizontal_edges_eq X F hh]

/-- Native actual cohomology cup pairing retains the same original determinant. -/
theorem cycleEvaluation_cup_periodicSquare (F : C(I × I, X))
    (hv : ∀ t, F (1, t) = F (0, t)) (hh : ∀ t, F (t, 0) = F (t, 1))
    (a b : cocycles k X 1) :
    cycleEvaluation k X 1 (periodicSquareChain X k F)
        (boundary_periodicSquareChain_eq_zero X k F hv hh)
        (cup k X (cocycleClass k X 1 a) (cocycleClass k X 1 b)) =
      values k X 1 (cocycleCochain k X 1 a) (edge X 2 (squarePositiveSimplex X F)) *
        values k X 1 (cocycleCochain k X 1 b) (edge X 2 (squareNegativeSimplex X F)) -
      values k X 1 (cocycleCochain k X 1 a) (edge X 2 (squareNegativeSimplex X F)) *
        values k X 1 (cocycleCochain k X 1 b) (edge X 2 (squarePositiveSimplex X F)) := by
  rw [cycleEvaluation_cup_cocycleClass, cupOne_periodicSquareChain X k F hv hh]

end ChenRanks.SingularCohomology
