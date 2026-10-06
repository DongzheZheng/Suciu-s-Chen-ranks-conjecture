import ChenRanks.RealTriangleAffineInjectivity
import ChenRanks.RealTriangleSixStrips

/-! Genuine injectivity of all six actual strip parametrizations.
Positive opposite coordinates handle the three boundary strips;
the three actual constructed degeneracy-line avoidances handle the
other strips. The actual last strip retains its required c,a order.
-/

noncomputable section

namespace ChenRanks

theorem realTriangleSixStrip_injective
    (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (ha : ∀ i j : Fin 3, 0 < a i j)
    (h₀₁ : realTrianglePlaneCoordinate (a 1) - realTrianglePlaneCoordinate (a 0) ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex 1) -
        realTrianglePlaneCoordinate (a 0)} : Set ℂ))
    (h₁₂ : realTrianglePlaneCoordinate (a 2) - realTrianglePlaneCoordinate (a 1) ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex 2) -
        realTrianglePlaneCoordinate (a 1)} : Set ℂ))
    (h₀₂ : realTrianglePlaneCoordinate (a 2) - realTrianglePlaneCoordinate (a 0) ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex 0) -
        realTrianglePlaneCoordinate (a 0)} : Set ℂ))
    (i : Fin 6) : Function.Injective
      (realTriangleAffineMap (realTriangleSixStripVertices a i)) := by
  fin_cases i
  · apply realTriangleAffineMap_injective_of_ordered_noncollinearity
    · exact realTrianglePlaneCoordinate_vertex_ne_vertex 0 1 (by decide)
    · exact realTrianglePlaneCoordinate_off_opposite_vertex_line
        (a 0) 2 1 0 (ha 0 2) (by decide) (by decide)
  · apply realTriangleAffineMap_injective_of_ordered_noncollinearity
    · exact (realTrianglePlaneCoordinate_ne_vertex_of_positive_coordinate
        (a 0) 0 1 (ha 0 0) (by decide)).symm
    · exact h₀₁
  · apply realTriangleAffineMap_injective_of_ordered_noncollinearity
    · exact realTrianglePlaneCoordinate_vertex_ne_vertex 1 2 (by decide)
    · exact realTrianglePlaneCoordinate_off_opposite_vertex_line
        (a 1) 0 2 1 (ha 1 0) (by decide) (by decide)
  · apply realTriangleAffineMap_injective_of_ordered_noncollinearity
    · exact (realTrianglePlaneCoordinate_ne_vertex_of_positive_coordinate
        (a 1) 0 2 (ha 1 0) (by decide)).symm
    · exact h₁₂
  · apply realTriangleAffineMap_injective_of_ordered_noncollinearity
    · exact realTrianglePlaneCoordinate_vertex_ne_vertex 2 0 (by decide)
    · exact realTrianglePlaneCoordinate_off_opposite_vertex_line
        (a 2) 1 0 2 (ha 2 1) (by decide) (by decide)
  · apply realTriangleAffineMap_injective_of_ordered_noncollinearity
    · exact (realTrianglePlaneCoordinate_ne_vertex_of_positive_coordinate
        (a 2) 1 0 (ha 2 1) (by decide)).symm
    · have hne : realTrianglePlaneCoordinate (stdSimplex.vertex 0) ≠
          realTrianglePlaneCoordinate (a 0) :=
        (realTrianglePlaneCoordinate_ne_vertex_of_positive_coordinate
          (a 0) 1 0 (ha 0 1) (by decide)).symm
      have h := singleton_span_nonmembership_shift_origin
        (realTrianglePlaneCoordinate (stdSimplex.vertex 0) - realTrianglePlaneCoordinate (a 0))
        (realTrianglePlaneCoordinate (a 2) - realTrianglePlaneCoordinate (a 0))
        (sub_ne_zero.mpr hne) h₀₂
      have hshift : (realTrianglePlaneCoordinate (stdSimplex.vertex 0) -
          realTrianglePlaneCoordinate (a 0)) - (realTrianglePlaneCoordinate (a 2) -
          realTrianglePlaneCoordinate (a 0)) =
          realTrianglePlaneCoordinate (stdSimplex.vertex 0) - realTrianglePlaneCoordinate (a 2) := by
        abel
      have hneg : -(realTrianglePlaneCoordinate (a 2) - realTrianglePlaneCoordinate (a 0)) =
          realTrianglePlaneCoordinate (a 0) - realTrianglePlaneCoordinate (a 2) := by abel
      simpa only [hshift, hneg] using h

end ChenRanks
