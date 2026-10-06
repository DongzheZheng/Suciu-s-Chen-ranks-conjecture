import ChenRanks.SingularSquareTriangleGeometry
import ChenRanks.SingularPathFunctoriality
import ChenRanks.SingularCupCocycles

/-!
# The actual boundary of a continuous triangle whose edges lie in U

Every face is an actual continuous map to the actual subspace U, with
its membership proof supplied by the literal boundary condition. When
the whole original triangle lies in U, its original native singular
two-simplex proves the closed-cochain boundary relation. No filling,
edge class, or expected relation is postulated.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (V : Type) [TopologicalSpace V] (U : Set V)

def partialTriangleFacePath (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (i : Fin 3) : C(I, U) where
  toFun t := ⟨F (realTriangleFacePath i t), hF i t⟩
  continuous_toFun := (F.continuous.comp (realTriangleFacePath i).continuous).subtype_mk (hF i)

variable (k : Type) [Field k]

def partialTriangleBoundaryValue (β : cochains k U 1)
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U) : k :=
  values k U 1 β (simplexOfPath U (partialTriangleFacePath V U F hF 1)) -
    values k U 1 β (simplexOfPath U (partialTriangleFacePath V U F hF 2)) -
    values k U 1 β (simplexOfPath U (partialTriangleFacePath V U F hF 0))

def simplexOfActualTriangle {X : Type} [TopologicalSpace X]
    (F : C(stdSimplex ℝ (Fin 3), X)) : simplices X 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).symm F

theorem geometricSimplex_simplexOfActualTriangle {X : Type} [TopologicalSpace X]
    (F : C(stdSimplex ℝ (Fin 3), X)) :
    geometricSimplex X 2 (simplexOfActualTriangle F) = F :=
  (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply _

theorem edge_simplexOfActualTriangle {X : Type} [TopologicalSpace X]
    (F : C(stdSimplex ℝ (Fin 3), X)) (i : Fin 3) :
    edge X i (simplexOfActualTriangle F) =
      simplexOfPath X (F.comp (realTriangleFacePath i)) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_edge, geometricSimplex_simplexOfActualTriangle,
    geometricSimplexPath_simplexOfPath]

/-- An actual whole triangle in U is a true native filling of its
actual three subspace-valued boundary paths. -/
theorem partialTriangleBoundaryValue_eq_zero_of_whole_triangle
    (β : cochains k U 1) (hβ : differential k U 1 β = 0)
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (hwhole : ∀ p : stdSimplex ℝ (Fin 3), F p ∈ U) :
    partialTriangleBoundaryValue V U k β F hF = 0 := by
  let G : C(stdSimplex ℝ (Fin 3), U) :=
    ⟨fun p => ⟨F p, hwhole p⟩, F.continuous.subtype_mk hwhole⟩
  have hface (i : Fin 3) : G.comp (realTriangleFacePath i) =
      partialTriangleFacePath V U F hF i := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    rfl
  have h := closedOne_triangle_relation k U β hβ (simplexOfActualTriangle G)
  simp only [edge_simplexOfActualTriangle, hface] at h
  unfold partialTriangleBoundaryValue
  linear_combination h

end ChenRanks.SingularCohomology
