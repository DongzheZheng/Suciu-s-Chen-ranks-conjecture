import ChenRanks.SingularPathCycles
import ChenRanks.SingularPathFunctoriality
import ChenRanks.SingularSquareTriangleGeometry

/-!
# The genuine singular triangle for concatenating two paths

The triangle is mapped into the actual concatenated path by the affine
parameter λ₁/2 + λ₂. Its three native faces are the original two paths
and their original concatenation, with the native boundary orientations.
This is an explicit geometric construction; no path-additivity or
singular-homotopy comparison is an input.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

/-- Recovering the native simplex from its actual geometric path loses
no information. -/
theorem simplexOfPath_geometricSimplexPath (s : simplices X 1) :
    simplexOfPath X (geometricSimplexPath X s) = s := by
  apply geometricSimplexPath_injective
  exact geometricSimplexPath_simplexOfPath X (geometricSimplexPath X s)

/-- The actual triangular parametrization of the concatenated path. -/
def pathConcatenationTriangleMap {x y z : X} (p : Path x y) (q : Path y z) :
    C(stdSimplex ℝ (Fin 3), X) where
  toFun t := (p.trans q).extend (t 1 / 2 + t 2)
  continuous_toFun := (p.trans q).continuous_extend.comp
    ((((continuous_apply 1).comp continuous_subtype_val).div_const 2).add
      ((continuous_apply 2).comp continuous_subtype_val))

/-- The exact affine parameter along each original native face. -/
private theorem pathConcatenationParameter_face (i : Fin 3) (t : I) :
    realTriangleFacePath i t 1 / 2 + realTriangleFacePath i t 2 =
      if i = 0 then (1 + (t : ℝ)) / 2
      else if i = 1 then (t : ℝ) else (t : ℝ) / 2 := by
  fin_cases i <;> simp [realTriangleFacePath_coordinate, Fin.succAbove] <;> ring

/-- The actual boundary consists of q, p⋆q, and p, in native face order. -/
theorem pathConcatenationTriangleMap_face {x y z : X}
    (p : Path x y) (q : Path y z) (i : Fin 3) (t : I) :
    pathConcatenationTriangleMap X p q (realTriangleFacePath i t) =
      if i = 0 then q t else if i = 1 then (p.trans q) t else p t := by
  change (p.trans q).extend
    (realTriangleFacePath i t 1 / 2 + realTriangleFacePath i t 2) = _
  rw [pathConcatenationParameter_face]
  fin_cases i
  · change (p.trans q).extend ((1 + (t : ℝ)) / 2) = q t
    rw [Path.extend_trans_of_half_le p q (by have ht := t.property.1; linarith)]
    have ht : 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ) := by ring
    rw [ht, Path.extend_extends']
  · change (p.trans q).extend (t : ℝ) = (p.trans q) t
    exact Path.extend_extends' (p.trans q) t
  · change (p.trans q).extend ((t : ℝ) / 2) = p t
    rw [Path.extend_trans_of_le_half p q (by have ht := t.property.2; linarith)]
    have ht : 2 * ((t : ℝ) / 2) = (t : ℝ) := by ring
    rw [ht, Path.extend_extends']

/-- The genuine native singular two-simplex of that actual triangle. -/
def pathConcatenationTriangle {x y z : X} (p : Path x y) (q : Path y z) :
    simplices X 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).symm (pathConcatenationTriangleMap X p q)

/-- This is the actual continuous triangle represented by the native simplex. -/
theorem geometricSimplex_pathConcatenationTriangle {x y z : X}
    (p : Path x y) (q : Path y z) :
    geometricSimplex X 2 (pathConcatenationTriangle X p q) =
      pathConcatenationTriangleMap X p q :=
  (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply _

/-- Native faces of the original constructed triangle are the exact
native simplices of the actual paths. -/
theorem edge_pathConcatenationTriangle {x y z : X}
    (p : Path x y) (q : Path y z) (i : Fin 3) :
    edge X i (pathConcatenationTriangle X p q) =
      if i = 0 then simplexOfPath X q.toContinuousMap
      else if i = 1 then simplexOfPath X (p.trans q).toContinuousMap
      else simplexOfPath X p.toContinuousMap := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_edge, geometricSimplex_pathConcatenationTriangle]
  fin_cases i <;> simp only [ite_true, ite_false,
    show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,
    geometricSimplexPath_simplexOfPath]
  all_goals
    apply ContinuousMap.ext
    intro t
    exact pathConcatenationTriangleMap_face X p q _ t

end ChenRanks.SingularCohomology
