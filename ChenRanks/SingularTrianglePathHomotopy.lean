import ChenRanks.RealSimplexPathHomotopy
import ChenRanks.SingularSimplexGeometricMaps

/-!
# The genuine triangle edge concatenation homotopy

The actual three cofaces have the actual ordered vertex endpoints.
Convex interpolation within the original real simplex gives a native
fixed-endpoint homotopy from the concatenated first two edges to the
diagonal. Mapping this homotopy by the original simplex supplies the
same statement for its actual geometric edges.
-/

noncomputable section

open AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

def realTriangleFirstEdge :
    Path (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 3)) (stdSimplex.vertex 1) where
  toContinuousMap := realTriangleFacePath 2
  source' := by simpa using realTriangleFacePath_zero 2
  target' := by simpa using realTriangleFacePath_one 2

def realTriangleSecondEdge :
    Path (stdSimplex.vertex 1 : stdSimplex ℝ (Fin 3)) (stdSimplex.vertex 2) where
  toContinuousMap := realTriangleFacePath 0
  source' := by simpa using realTriangleFacePath_zero 0
  target' := by simpa using realTriangleFacePath_one 0

def realTriangleDiagonalEdge :
    Path (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 3)) (stdSimplex.vertex 2) where
  toContinuousMap := realTriangleFacePath 1
  source' := by simpa using realTriangleFacePath_zero 1
  target' := by simpa using realTriangleFacePath_one 1

def realTriangleEdgeConcatenationHomotopy :
    (realTriangleFirstEdge.trans realTriangleSecondEdge).Homotopy realTriangleDiagonalEdge :=
  realSimplexPathHomotopy 2 _ _

variable {X : Type} [TopologicalSpace X]

def triangleFirstEdgePath (s : C(stdSimplex ℝ (Fin 3), X)) :
    Path (s (stdSimplex.vertex 0)) (s (stdSimplex.vertex 1)) :=
  realTriangleFirstEdge.map s.continuous

def triangleSecondEdgePath (s : C(stdSimplex ℝ (Fin 3), X)) :
    Path (s (stdSimplex.vertex 1)) (s (stdSimplex.vertex 2)) :=
  realTriangleSecondEdge.map s.continuous

def triangleDiagonalEdgePath (s : C(stdSimplex ℝ (Fin 3), X)) :
    Path (s (stdSimplex.vertex 0)) (s (stdSimplex.vertex 2)) :=
  realTriangleDiagonalEdge.map s.continuous

def triangleEdgeConcatenationHomotopy (s : C(stdSimplex ℝ (Fin 3), X)) :
    ((triangleFirstEdgePath s).trans (triangleSecondEdgePath s)).Homotopy
      (triangleDiagonalEdgePath s) := by
  have H := realTriangleEdgeConcatenationHomotopy.map s
  simpa only [Path.map_trans, triangleFirstEdgePath, triangleSecondEdgePath,
    triangleDiagonalEdgePath] using H

end ChenRanks.SingularCohomology
