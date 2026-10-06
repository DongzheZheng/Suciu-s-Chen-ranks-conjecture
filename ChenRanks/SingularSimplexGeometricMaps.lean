import ChenRanks.SingularCupOne
import Mathlib.AlgebraicTopology.SingularSet

/-!
# The actual geometric maps underlying native singular simplices

The native singular-set equivalence recovers the original continuous map
on the real standard simplex. Native simplicial faces are proved to be
the actual geometric cofaces. The actual one-simplex is parametrized by
the library's standard-simplex/unit-interval homeomorphism.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

/-- The original continuous map represented by the native singular simplex. -/
def geometricSimplex (n : ℕ) (s : simplices X n) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk n)) s

/-- The actual geometric coface used by the native singular functor. -/
def realSimplexFaceMap (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (SimplexCategory.δ i), stdSimplex.continuous_map _⟩

/-- The native singular face has exactly its original geometric meaning. -/
theorem geometricSimplex_face (n : ℕ) (i : Fin (n + 2))
    (s : simplices X (n + 1)) (x : stdSimplex ℝ (Fin (n + 1))) :
    geometricSimplex X n ((TopCat.toSSet.obj (TopCat.of X)).δ i s) x =
      geometricSimplex X (n + 1) s (realSimplexFaceMap n i x) := by
  rfl

/-- The original one-simplex's actual unit-interval parametrization. -/
def realSimplexIntervalMap : C(I, stdSimplex ℝ (Fin 2)) :=
  ⟨stdSimplexHomeomorphUnitInterval.symm,
    stdSimplexHomeomorphUnitInterval.symm.continuous⟩

theorem realSimplexIntervalMap_zero :
    realSimplexIntervalMap 0 = (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 2)) := by
  apply stdSimplexHomeomorphUnitInterval.injective
  change stdSimplexHomeomorphUnitInterval
      (stdSimplexHomeomorphUnitInterval.symm 0) =
    stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 0)
  rw [Homeomorph.apply_symm_apply, stdSimplexHomeomorphUnitInterval_zero]

theorem realSimplexIntervalMap_one :
    realSimplexIntervalMap 1 = (stdSimplex.vertex 1 : stdSimplex ℝ (Fin 2)) := by
  apply stdSimplexHomeomorphUnitInterval.injective
  change stdSimplexHomeomorphUnitInterval
      (stdSimplexHomeomorphUnitInterval.symm 1) =
    stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 1)
  rw [Homeomorph.apply_symm_apply, stdSimplexHomeomorphUnitInterval_one]

/-- The true geometric path of the same native singular one-simplex. -/
def geometricSimplexPath (s : simplices X 1) : C(I, X) :=
  (geometricSimplex X 1 s).comp realSimplexIntervalMap

/-- The actual standard-triangle edge parametrization. -/
def realTriangleFacePath (i : Fin 3) : C(I, stdSimplex ℝ (Fin 3)) :=
  (realSimplexFaceMap 1 i).comp realSimplexIntervalMap

theorem realTriangleFacePath_zero (i : Fin 3) :
    realTriangleFacePath i 0 = stdSimplex.vertex (i.succAbove 0) := by
  change realSimplexFaceMap 1 i (realSimplexIntervalMap 0) = _
  rw [realSimplexIntervalMap_zero]
  exact stdSimplex.map_vertex (SimplexCategory.δ i) 0

theorem realTriangleFacePath_one (i : Fin 3) :
    realTriangleFacePath i 1 = stdSimplex.vertex (i.succAbove 1) := by
  change realSimplexFaceMap 1 i (realSimplexIntervalMap 1) = _
  rw [realSimplexIntervalMap_one]
  exact stdSimplex.map_vertex (SimplexCategory.δ i) 1

/-- Native triangle faces give exactly these original edge paths. -/
theorem geometricSimplexPath_edge (s : simplices X 2) (i : Fin 3) :
    geometricSimplexPath X (edge X i s) =
      (geometricSimplex X 2 s).comp (realTriangleFacePath i) := by
  ext t
  exact geometricSimplex_face X 1 i s (realSimplexIntervalMap t)

end ChenRanks.SingularCohomology
