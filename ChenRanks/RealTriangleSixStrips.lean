import ChenRanks.RealTriangleAffineSubdivision
import Mathlib.Tactic

/-!
# Actual ordered six strips around a selected puncture

The true ordered vertices give six genuine affine maps into the
original standard triangle. Strict barycentric sector inequalities
exclude the selected original puncture from every entire strip.
The alternating six-boundary identity is a literal cancellation of
the shared oriented edges, with no covering or multiplicity premise.
-/

noncomputable section

namespace ChenRanks

def realTriangleSixStripVertices (a : Fin 3 → stdSimplex ℝ (Fin 3)) :
    Fin 6 → Fin 3 → stdSimplex ℝ (Fin 3) :=
  ![![stdSimplex.vertex 0, stdSimplex.vertex 1, a 0],
    ![stdSimplex.vertex 1, a 0, a 1],
    ![stdSimplex.vertex 1, stdSimplex.vertex 2, a 1],
    ![stdSimplex.vertex 2, a 1, a 2],
    ![stdSimplex.vertex 2, stdSimplex.vertex 0, a 2],
    ![stdSimplex.vertex 0, a 2, a 0]]

def realTriangleSixStripOmittedCoordinate : Fin 6 → Fin 3 := ![2, 2, 0, 0, 1, 1]

theorem realTriangleSixStrip_vertex_coordinate_lt
    (p : stdSimplex ℝ (Fin 3)) (hp : ∀ j : Fin 3, 0 < p j)
    (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (ha : ∀ (i j : Fin 3), j ≠ i → a i j < p j)
    (i : Fin 6) (r : Fin 3) :
    realTriangleSixStripVertices a i r (realTriangleSixStripOmittedCoordinate i) <
      p (realTriangleSixStripOmittedCoordinate i) := by
  fin_cases i <;> fin_cases r <;>
    simp [realTriangleSixStripVertices, realTriangleSixStripOmittedCoordinate,
      stdSimplex.vertex, Pi.single_apply]
  all_goals
    first
    | exact hp 0
    | exact hp 1
    | exact hp 2
    | exact ha 0 2 (by decide)
    | exact ha 1 2 (by decide)
    | exact ha 1 0 (by decide)
    | exact ha 2 0 (by decide)
    | exact ha 2 1 (by decide)
    | exact ha 0 1 (by decide)

/-- Every actual affine strip excludes the chosen puncture everywhere,
as a consequence of the actual strict sector coordinates. -/
theorem realTriangleSixStrip_ne_selected_point
    (p : stdSimplex ℝ (Fin 3)) (hp : ∀ j : Fin 3, 0 < p j)
    (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (ha : ∀ (i j : Fin 3), j ≠ i → a i j < p j)
    (i : Fin 6) (q : stdSimplex ℝ (Fin 3)) :
    realTriangleAffineMap (realTriangleSixStripVertices a i) q ≠ p :=
  realTriangleAffineMap_ne_of_coordinate_lt _ p
    (realTriangleSixStripOmittedCoordinate i)
    (realTriangleSixStrip_vertex_coordinate_lt p hp a ha i) q

/-- The six actual oriented triangle relations cancel all shared
edges. The inner cycle has the actual vertex order a,b,c. -/
theorem sixOrderedTriangleRelations_boundary_equal
    {V k : Type*} [Field k] (L : V → V → k) (A B C a b c : V)
    (h₀ : L B a - L A a + L A B = 0)
    (h₁ : L a b - L B b + L B a = 0)
    (h₂ : L C b - L B b + L B C = 0)
    (h₃ : L b c - L C c + L C b = 0)
    (h₄ : L A c - L C c + L C A = 0)
    (h₅ : L c a - L A a + L A c = 0) :
    L A B + L B C + L C A = L a b + L b c + L c a := by
  linear_combination h₀ - h₁ + h₂ - h₃ + h₄ - h₅

end ChenRanks
