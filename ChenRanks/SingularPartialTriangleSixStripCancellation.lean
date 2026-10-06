import ChenRanks.SingularPartialTriangleSegments
import ChenRanks.RealTrianglePunctureRemovalGeometry

/-!
# Native oriented boundary cancellation for the actual six strips

The six actual boundary-zero conclusions are exactly the conclusions
used by finite-puncture induction. Each is the actual singular
closed-cochain value of its own genuine subspace-valued three edges.
The original and inner boundary identity is derived from those literal
relations and the proved native reversal identity.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (V : Type) [TopologicalSpace V] (U : Set V) (k : Type) [Field k]

theorem partialTriangleFace_value_eq_segment
    (β : cochains k U 1) (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (i : Fin 3) :
    values k U 1 β (simplexOfPath U (partialTriangleFacePath V U F hF i)) =
      partialTriangleSegmentValue V U k β F
        (stdSimplex.vertex (i.succAbove 0)) (stdSimplex.vertex (i.succAbove 1)) := by
  have hs : ∀ t : I, F (realTriangleSegmentPath
      (stdSimplex.vertex (i.succAbove 0)) (stdSimplex.vertex (i.succAbove 1)) t) ∈ U := by
    intro t
    rw [realTriangleSegmentPath_native_face]
    exact hF i t
  rw [partialTriangleSegmentValue_of_safe V U k β F _ _ hs]
  have heq : partialTriangleFacePath V U F hF i =
      partialTriangleSegmentPath V U F
        (stdSimplex.vertex (i.succAbove 0)) (stdSimplex.vertex (i.succAbove 1)) hs := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change F (realTriangleFacePath i t) = F (realTriangleSegmentPath
      (stdSimplex.vertex (i.succAbove 0)) (stdSimplex.vertex (i.succAbove 1)) t)
    rw [realTriangleSegmentPath_native_face]
  rw [heq]

theorem partialTriangleBoundaryValue_eq_segments
    (β : cochains k U 1) (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U) :
    partialTriangleBoundaryValue V U k β F hF =
      partialTriangleSegmentValue V U k β F (stdSimplex.vertex 0) (stdSimplex.vertex 2) -
        partialTriangleSegmentValue V U k β F (stdSimplex.vertex 0) (stdSimplex.vertex 1) -
        partialTriangleSegmentValue V U k β F (stdSimplex.vertex 1) (stdSimplex.vertex 2) := by
  unfold partialTriangleBoundaryValue
  rw [partialTriangleFace_value_eq_segment, partialTriangleFace_value_eq_segment,
    partialTriangleFace_value_eq_segment]
  simp [Fin.succAbove]

/-- The boundary value of the original actual triangle equals that
of the actual inner triangle when the six actual strip boundaries
vanish. This is a literal oriented-edge cancellation. -/
theorem partialTriangleSixStrips_originalBoundary_eq_innerBoundary
    (β : cochains k U 1) (hβ : differential k U 1 β = 0)
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (hstrips : ∀ (i : Fin 6) (r : Fin 3) (t : I),
      F (realTriangleAffineMap (realTriangleSixStripVertices a i) (realTriangleFacePath r t)) ∈ U)
    (hinner : ∀ (r : Fin 3) (t : I),
      F (realTriangleAffineMap a (realTriangleFacePath r t)) ∈ U)
    (hzero : ∀ i : Fin 6, partialTriangleBoundaryValue V U k β
      (F.comp (realTriangleAffineMap (realTriangleSixStripVertices a i))) (hstrips i) = 0) :
    partialTriangleBoundaryValue V U k β F hF =
      partialTriangleBoundaryValue V U k β (F.comp (realTriangleAffineMap a)) hinner := by
  let L := partialTriangleSegmentValue V U k β F
  have hs (i : Fin 6) :
      L (realTriangleSixStripVertices a i 0) (realTriangleSixStripVertices a i 2) -
        L (realTriangleSixStripVertices a i 0) (realTriangleSixStripVertices a i 1) -
        L (realTriangleSixStripVertices a i 1) (realTriangleSixStripVertices a i 2) = 0 := by
    have h := hzero i
    rw [partialTriangleBoundaryValue_affineMap_eq_segments] at h
    exact h
  have h₀ := hs 0
  have h₁ := hs 1
  have h₂ := hs 2
  have h₃ := hs 3
  have h₄ := hs 4
  have h₅ := hs 5
  change L (stdSimplex.vertex 0) (a 0) - L (stdSimplex.vertex 0) (stdSimplex.vertex 1) -
    L (stdSimplex.vertex 1) (a 0) = 0 at h₀
  change L (stdSimplex.vertex 1) (a 1) - L (stdSimplex.vertex 1) (a 0) -
    L (a 0) (a 1) = 0 at h₁
  change L (stdSimplex.vertex 1) (a 1) - L (stdSimplex.vertex 1) (stdSimplex.vertex 2) -
    L (stdSimplex.vertex 2) (a 1) = 0 at h₂
  change L (stdSimplex.vertex 2) (a 2) - L (stdSimplex.vertex 2) (a 1) -
    L (a 1) (a 2) = 0 at h₃
  change L (stdSimplex.vertex 2) (a 2) - L (stdSimplex.vertex 2) (stdSimplex.vertex 0) -
    L (stdSimplex.vertex 0) (a 2) = 0 at h₄
  change L (stdSimplex.vertex 0) (a 0) - L (stdSimplex.vertex 0) (a 2) -
    L (a 2) (a 0) = 0 at h₅
  have hc := sixOrderedTriangleRelations_boundary_equal L
    (stdSimplex.vertex 0) (stdSimplex.vertex 1) (stdSimplex.vertex 2) (a 0) (a 1) (a 2)
    (by linear_combination -h₀) (by linear_combination -h₁)
    (by linear_combination -h₂) (by linear_combination -h₃)
    (by linear_combination -h₄) (by linear_combination -h₅)
  have houterSafe : ∀ t : I,
      F (realTriangleSegmentPath (stdSimplex.vertex 0) (stdSimplex.vertex 2) t) ∈ U := by
    intro t
    have heq : realTriangleSegmentPath (stdSimplex.vertex 0) (stdSimplex.vertex 2) t =
        realTriangleFacePath 1 t := by
      simpa [Fin.succAbove] using realTriangleSegmentPath_native_face (i := 1) t
    rw [heq]
    exact hF 1 t
  have hinnerSafe : ∀ t : I, F (realTriangleSegmentPath (a 0) (a 2) t) ∈ U := by
    intro t
    have heq : realTriangleAffineMap a (realTriangleFacePath 1 t) =
        realTriangleSegmentPath (a 0) (a 2) t := by
      simpa [Fin.succAbove] using realTriangleAffineMap_face_eq_segment (v := a) (i := 1) t
    rw [← heq]
    exact hinner 1 t
  have hro : L (stdSimplex.vertex 2) (stdSimplex.vertex 0) =
      -L (stdSimplex.vertex 0) (stdSimplex.vertex 2) :=
    partialTriangleSegmentValue_reverse V U k β hβ F _ _ houterSafe
  have hri : L (a 2) (a 0) = -L (a 0) (a 2) :=
    partialTriangleSegmentValue_reverse V U k β hβ F _ _ hinnerSafe
  rw [partialTriangleBoundaryValue_eq_segments,
    partialTriangleBoundaryValue_affineMap_eq_segments]
  change L (stdSimplex.vertex 0) (stdSimplex.vertex 2) -
      L (stdSimplex.vertex 0) (stdSimplex.vertex 1) - L (stdSimplex.vertex 1) (stdSimplex.vertex 2) =
    L (a 0) (a 2) - L (a 0) (a 1) - L (a 1) (a 2)
  linear_combination -hc + hro - hri

end ChenRanks.SingularCohomology
