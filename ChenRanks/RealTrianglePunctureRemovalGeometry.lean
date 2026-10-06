import ChenRanks.RealTrianglePunctureFreeEdges
import ChenRanks.RealTriangleSixStripsInjectivity
import ChenRanks.FinitePuncturePreimageDecrease
import ChenRanks.RealTriangleBoundaryPoints

/-!
# Genuine removal geometry for one actual triangle puncture

The boundary condition derives interiority of the selected bad point.
Actual finite-line avoidance constructs the three nearby vertices.
Their genuine coordinate, edge, and nondegeneracy properties prove
all six new boundaries avoid the original bad set and every true
bad-point preimage has strictly smaller cardinal. No removal package,
smaller cardinal, or favorable vertex is an input.
-/

noncomputable section

open unitInterval

namespace ChenRanks

theorem realTriangleSegmentPath_native_face (i : Fin 3) (t : I) :
    realTriangleSegmentPath (stdSimplex.vertex (i.succAbove 0))
      (stdSimplex.vertex (i.succAbove 1)) t = SingularCohomology.realTriangleFacePath i t := by
  apply Subtype.ext
  funext j
  change realTriangleSegmentPath (stdSimplex.vertex (i.succAbove 0))
    (stdSimplex.vertex (i.succAbove 1)) t j = SingularCohomology.realTriangleFacePath i t j
  rw [realTriangleSegmentPath_coordinate, SingularCohomology.realTriangleFacePath_coordinate]
  fin_cases i <;> fin_cases j <;> simp [Fin.succAbove, stdSimplex.vertex, Pi.single_apply]

/-- The actual geometry needed by finite-puncture induction is fully
constructed from the actual bad set, actual selected member, and radius. -/
theorem exists_actual_realTriangle_puncture_removal_geometry
    (B : Set (stdSimplex ℝ (Fin 3))) (hB : B.Finite)
    (hboundary : ∀ (i : Fin 3) (t : I), SingularCohomology.realTriangleFacePath i t ∉ B)
    (p : stdSimplex ℝ (Fin 3)) (hp : p ∈ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Fin 3 → stdSimplex ℝ (Fin 3),
      (∀ i j : Fin 3, 0 < a i j) ∧
      (∀ (i : Fin 3), dist (realTrianglePlaneCoordinate (a i))
        (realTrianglePlaneCoordinate p) < ε) ∧
      (∀ (i : Fin 6) (r : Fin 3) (t : I),
        realTriangleAffineMap (realTriangleSixStripVertices a i)
          (SingularCohomology.realTriangleFacePath r t) ∉ B) ∧
      (∀ (r : Fin 3) (t : I), realTriangleAffineMap a
        (SingularCohomology.realTriangleFacePath r t) ∉ B) ∧
      (∀ i : Fin 6,
        Function.Injective (realTriangleAffineMap (realTriangleSixStripVertices a i)) ∧
        (∀ q, realTriangleAffineMap (realTriangleSixStripVertices a i) q ≠ p) ∧
        ((realTriangleAffineMap (realTriangleSixStripVertices a i)) ⁻¹' B).Finite ∧
        ((realTriangleAffineMap (realTriangleSixStripVertices a i)) ⁻¹' B).ncard < B.ncard) := by
  have hpinterior := realTrianglePoint_coordinates_positive_of_boundary_avoidance B hboundary p hp
  obtain ⟨a₀, a₁, a₂, h₀, h₁, h₂, ho₀, ho₁, ho₂, hi₀₁, hi₀₂, hi₁₂, hn₀₁, hn₁₂, hn₀₂⟩ :=
    exists_realTriangle_three_inner_vertices B hB p hpinterior ε hε
  let a : Fin 3 → stdSimplex ℝ (Fin 3) := ![a₀, a₁, a₂]
  have hpos : ∀ i j : Fin 3, 0 < a i j := by
    intro i j
    fin_cases i
    · exact h₀.1 j
    · exact h₁.1 j
    · exact h₂.1 j
  have hsector : ∀ (i j : Fin 3), j ≠ i → a i j < p j := by
    intro i j hji
    fin_cases i
    · exact h₀.2.1 j hji
    · exact h₁.2.1 j hji
    · exact h₂.2.1 j hji
  have hnear : ∀ i : Fin 3, dist (realTrianglePlaneCoordinate (a i))
      (realTrianglePlaneCoordinate p) < ε := by
    intro i
    fin_cases i
    · exact h₀.2.2
    · exact h₁.2.2
    · exact h₂.2.2
  have houter : ∀ i : Fin 3, realTriangleVertexOuterLineAvoidance B (a i) := by
    intro i
    fin_cases i
    · exact ho₀
    · exact ho₁
    · exact ho₂
  have hvertex : ∀ j : Fin 3, (stdSimplex.vertex j : stdSimplex ℝ (Fin 3)) ∉ B := by
    intro j
    fin_cases j
    · simpa only [SingularCohomology.realTriangleFacePath_zero] using hboundary 2 0
    · simpa only [SingularCohomology.realTriangleFacePath_one] using hboundary 2 1
    · simpa only [SingularCohomology.realTriangleFacePath_one] using hboundary 0 1
  have hbsegments : ∀ i : Fin 3, realTriangleSegmentAvoids B
      (stdSimplex.vertex (i.succAbove 0)) (stdSimplex.vertex (i.succAbove 1)) := by
    intro i t
    rw [realTriangleSegmentPath_native_face]
    exact hboundary i t
  have he := realTriangleSixStrips_faces_avoid_bad_set B hvertex hbsegments a
    houter hi₀₁ hi₀₂ hi₁₂
  refine ⟨a, hpos, hnear, he.1, he.2, ?_⟩
  intro i
  have hinj := realTriangleSixStrip_injective a hpos hn₀₁ hn₁₂ hn₀₂ i
  have hexclude := realTriangleSixStrip_ne_selected_point p hpinterior a hsector i
  have hsmall := finitePuncturePreimage_ncard_lt _ hinj B hB p hp hexclude
  exact ⟨hinj, hexclude, hsmall.1, hsmall.2⟩

end ChenRanks
