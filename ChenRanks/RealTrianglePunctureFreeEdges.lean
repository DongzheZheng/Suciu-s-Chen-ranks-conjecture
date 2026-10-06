import ChenRanks.RealTriangleThreeInnerVertices
import ChenRanks.RealTriangleSixStrips
import Mathlib.Tactic

/-!
# Genuine new triangle edges avoid the actual finite punctures

The native face parametrizations equal the actual ordered real
segments. The line avoidances constructed from the original punctures
then prove that every shared edge and every inner edge misses the
original bad set. Reversal is derived from the actual segment formula.
-/

noncomputable section

open unitInterval

namespace ChenRanks

def realTriangleSegmentPath (a b : stdSimplex ℝ (Fin 3)) :
    C(I, stdSimplex ℝ (Fin 3)) :=
  (realTriangleAffineMap ![a, b, b]).comp (SingularCohomology.realTriangleFacePath 2)

theorem realTriangleSegmentPath_coordinate (a b : stdSimplex ℝ (Fin 3))
    (t : I) (j : Fin 3) : realTriangleSegmentPath a b t j =
      (1 - (t : ℝ)) * a j + (t : ℝ) * b j := by
  exact realTriangleAffineMap_face_coordinate ![a, b, b] 2 t j

theorem realTriangleSegmentPath_plane (a b : stdSimplex ℝ (Fin 3)) (t : I) :
    realTrianglePlaneCoordinate (realTriangleSegmentPath a b t) =
      (1 - (t : ℝ)) • realTrianglePlaneCoordinate a +
        (t : ℝ) • realTrianglePlaneCoordinate b := by
  have hRe (p : stdSimplex ℝ (Fin 3)) : (realTrianglePlaneCoordinate p).re = p 0 := by
    simp [realTrianglePlaneCoordinate]
  have hIm (p : stdSimplex ℝ (Fin 3)) : (realTrianglePlaneCoordinate p).im = p 1 := by
    simp [realTrianglePlaneCoordinate]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hRe]
    exact realTriangleSegmentPath_coordinate a b t 0
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hIm]
    exact realTriangleSegmentPath_coordinate a b t 1

def realTriangleSegmentAvoids (B : Set (stdSimplex ℝ (Fin 3)))
    (a b : stdSimplex ℝ (Fin 3)) : Prop :=
  ∀ t : I, realTriangleSegmentPath a b t ∉ B

theorem realTriangleSegmentAvoids_of_line_avoidance
    (B : Set (stdSimplex ℝ (Fin 3))) (a b : stdSimplex ℝ (Fin 3))
    (ha : a ∉ B)
    (hab : ∀ q, q ∈ B →
      realTrianglePlaneCoordinate b - realTrianglePlaneCoordinate a ∉
        Submodule.span ℝ ({realTrianglePlaneCoordinate q - realTrianglePlaneCoordinate a} : Set ℂ)) :
    realTriangleSegmentAvoids B a b := by
  intro t hbad
  have hne : realTriangleSegmentPath a b t ≠ a := by
    intro h
    apply ha
    rwa [h] at hbad
  have hplaneNe : realTrianglePlaneCoordinate (realTriangleSegmentPath a b t) ≠
      realTrianglePlaneCoordinate a :=
    fun h => hne (realTrianglePlaneCoordinate_injective h)
  have havoid := realWeightedEdge_ne_of_line_avoidance
    (realTrianglePlaneCoordinate a) (realTrianglePlaneCoordinate b)
    (realTrianglePlaneCoordinate (realTriangleSegmentPath a b t)) hplaneNe
    (hab _ hbad) (t : ℝ)
  exact havoid (realTriangleSegmentPath_plane a b t).symm

theorem realTriangleSegmentAvoids_symm
    (B : Set (stdSimplex ℝ (Fin 3))) (a b : stdSimplex ℝ (Fin 3))
    (h : realTriangleSegmentAvoids B a b) : realTriangleSegmentAvoids B b a := by
  intro t ht
  let s : I := ⟨1 - (t : ℝ), sub_nonneg.mpr t.property.2, by linarith [t.property.1]⟩
  have heq : realTriangleSegmentPath a b s = realTriangleSegmentPath b a t := by
    apply Subtype.ext
    funext j
    change realTriangleSegmentPath a b s j = realTriangleSegmentPath b a t j
    rw [realTriangleSegmentPath_coordinate, realTriangleSegmentPath_coordinate]
    dsimp only [s]
    ring
  apply h s
  rwa [heq]

theorem realTriangleAffineMap_face_eq_segment
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (i : Fin 3) (t : I) :
    realTriangleAffineMap v (SingularCohomology.realTriangleFacePath i t) =
      realTriangleSegmentPath (v (i.succAbove 0)) (v (i.succAbove 1)) t := by
  apply Subtype.ext
  funext j
  change realTriangleAffineMap v (SingularCohomology.realTriangleFacePath i t) j =
    realTriangleSegmentPath (v (i.succAbove 0)) (v (i.succAbove 1)) t j
  rw [realTriangleAffineMap_face_coordinate, realTriangleSegmentPath_coordinate]

theorem realTriangleVertex_not_bad_of_outerLineAvoidance
    (B : Set (stdSimplex ℝ (Fin 3))) (a : stdSimplex ℝ (Fin 3))
    (ha : realTriangleVertexOuterLineAvoidance B a) : a ∉ B := by
  intro hbad
  apply ha a hbad 0
  exact Submodule.mem_span_singleton_self _

theorem realTriangleAffineMap_faces_avoid_of_three_segments
    (B : Set (stdSimplex ℝ (Fin 3))) (v : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (v 1) (v 2))
    (h₁ : realTriangleSegmentAvoids B (v 0) (v 2))
    (h₂ : realTriangleSegmentAvoids B (v 0) (v 1))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap v (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  rw [realTriangleAffineMap_face_eq_segment]
  fin_cases r
  · exact h₀ t
  · exact h₁ t
  · exact h₂ t

private theorem actualStrip0_faces_avoid
    (B : Set (stdSimplex ℝ (Fin 3))) (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (stdSimplex.vertex 1) (a 0))
    (h₁ : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (a 0))
    (h₂ : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (stdSimplex.vertex 1))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap (realTriangleSixStripVertices a 0)
      (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  change realTriangleAffineMap ![stdSimplex.vertex 0, stdSimplex.vertex 1, a 0]
    (SingularCohomology.realTriangleFacePath r t) ∉ B
  exact realTriangleAffineMap_faces_avoid_of_three_segments B
    ![stdSimplex.vertex 0, stdSimplex.vertex 1, a 0] h₀ h₁ h₂ r t

private theorem actualStrip1_faces_avoid
    (B : Set (stdSimplex ℝ (Fin 3))) (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (a 0) (a 1))
    (h₁ : realTriangleSegmentAvoids B (stdSimplex.vertex 1) (a 1))
    (h₂ : realTriangleSegmentAvoids B (stdSimplex.vertex 1) (a 0))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap (realTriangleSixStripVertices a 1)
      (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  change realTriangleAffineMap ![stdSimplex.vertex 1, a 0, a 1]
    (SingularCohomology.realTriangleFacePath r t) ∉ B
  exact realTriangleAffineMap_faces_avoid_of_three_segments B
    ![stdSimplex.vertex 1, a 0, a 1] h₀ h₁ h₂ r t

private theorem actualStrip2_faces_avoid
    (B : Set (stdSimplex ℝ (Fin 3))) (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (stdSimplex.vertex 2) (a 1))
    (h₁ : realTriangleSegmentAvoids B (stdSimplex.vertex 1) (a 1))
    (h₂ : realTriangleSegmentAvoids B (stdSimplex.vertex 1) (stdSimplex.vertex 2))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap (realTriangleSixStripVertices a 2)
      (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  change realTriangleAffineMap ![stdSimplex.vertex 1, stdSimplex.vertex 2, a 1]
    (SingularCohomology.realTriangleFacePath r t) ∉ B
  exact realTriangleAffineMap_faces_avoid_of_three_segments B
    ![stdSimplex.vertex 1, stdSimplex.vertex 2, a 1] h₀ h₁ h₂ r t

private theorem actualStrip3_faces_avoid
    (B : Set (stdSimplex ℝ (Fin 3))) (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (a 1) (a 2))
    (h₁ : realTriangleSegmentAvoids B (stdSimplex.vertex 2) (a 2))
    (h₂ : realTriangleSegmentAvoids B (stdSimplex.vertex 2) (a 1))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap (realTriangleSixStripVertices a 3)
      (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  change realTriangleAffineMap ![stdSimplex.vertex 2, a 1, a 2]
    (SingularCohomology.realTriangleFacePath r t) ∉ B
  exact realTriangleAffineMap_faces_avoid_of_three_segments B
    ![stdSimplex.vertex 2, a 1, a 2] h₀ h₁ h₂ r t

private theorem actualStrip4_faces_avoid
    (B : Set (stdSimplex ℝ (Fin 3))) (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (a 2))
    (h₁ : realTriangleSegmentAvoids B (stdSimplex.vertex 2) (a 2))
    (h₂ : realTriangleSegmentAvoids B (stdSimplex.vertex 2) (stdSimplex.vertex 0))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap (realTriangleSixStripVertices a 4)
      (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  change realTriangleAffineMap ![stdSimplex.vertex 2, stdSimplex.vertex 0, a 2]
    (SingularCohomology.realTriangleFacePath r t) ∉ B
  exact realTriangleAffineMap_faces_avoid_of_three_segments B
    ![stdSimplex.vertex 2, stdSimplex.vertex 0, a 2] h₀ h₁ h₂ r t

private theorem actualStrip5_faces_avoid
    (B : Set (stdSimplex ℝ (Fin 3))) (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTriangleSegmentAvoids B (a 2) (a 0))
    (h₁ : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (a 0))
    (h₂ : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (a 2))
    (r : Fin 3) (t : I) :
    realTriangleAffineMap (realTriangleSixStripVertices a 5)
      (SingularCohomology.realTriangleFacePath r t) ∉ B := by
  change realTriangleAffineMap ![stdSimplex.vertex 0, a 2, a 0]
    (SingularCohomology.realTriangleFacePath r t) ∉ B
  exact realTriangleAffineMap_faces_avoid_of_three_segments B
    ![stdSimplex.vertex 0, a 2, a 0] h₀ h₁ h₂ r t

/-- All genuinely new shared edges and inner edges are derived from
the actual line-avoidance data constructed by the three-vertex factory.
Only the actual original boundary edges are supplied as such. -/
theorem realTriangleSixStrips_faces_avoid_bad_set
    (B : Set (stdSimplex ℝ (Fin 3)))
    (hvertex : ∀ j : Fin 3, (stdSimplex.vertex j : stdSimplex ℝ (Fin 3)) ∉ B)
    (hboundary : ∀ i : Fin 3,
      realTriangleSegmentAvoids B (stdSimplex.vertex (i.succAbove 0))
        (stdSimplex.vertex (i.succAbove 1)))
    (a : Fin 3 → stdSimplex ℝ (Fin 3))
    (houter : ∀ i : Fin 3, realTriangleVertexOuterLineAvoidance B (a i))
    (h₀₁ : realTriangleVertexInnerLineAvoidance B (a 0) (a 1))
    (h₀₂ : realTriangleVertexInnerLineAvoidance B (a 0) (a 2))
    (h₁₂ : realTriangleVertexInnerLineAvoidance B (a 1) (a 2)) :
    (∀ (i : Fin 6) (r : Fin 3) (t : I),
      realTriangleAffineMap (realTriangleSixStripVertices a i)
        (SingularCohomology.realTriangleFacePath r t) ∉ B) ∧
    (∀ (r : Fin 3) (t : I),
      realTriangleAffineMap a (SingularCohomology.realTriangleFacePath r t) ∉ B) := by
  have ho (i j : Fin 3) : realTriangleSegmentAvoids B (stdSimplex.vertex j) (a i) :=
    realTriangleSegmentAvoids_of_line_avoidance B _ _ (hvertex j)
      (fun q hq => houter i q hq j)
  have ha (i : Fin 3) : a i ∉ B :=
    realTriangleVertex_not_bad_of_outerLineAvoidance B (a i) (houter i)
  have h01 := realTriangleSegmentAvoids_of_line_avoidance B _ _ (ha 0) h₀₁
  have h02 := realTriangleSegmentAvoids_of_line_avoidance B _ _ (ha 0) h₀₂
  have h12 := realTriangleSegmentAvoids_of_line_avoidance B _ _ (ha 1) h₁₂
  have h20 := realTriangleSegmentAvoids_symm B _ _ h02
  have hAB : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (stdSimplex.vertex 1) := hboundary 2
  have hBC : realTriangleSegmentAvoids B (stdSimplex.vertex 1) (stdSimplex.vertex 2) := hboundary 0
  have hAC : realTriangleSegmentAvoids B (stdSimplex.vertex 0) (stdSimplex.vertex 2) := hboundary 1
  have hCA := realTriangleSegmentAvoids_symm B _ _ hAC
  constructor
  · intro i r t
    fin_cases i
    · exact actualStrip0_faces_avoid B a (ho 0 1) (ho 0 0) hAB r t
    · exact actualStrip1_faces_avoid B a h01 (ho 1 1) (ho 0 1) r t
    · exact actualStrip2_faces_avoid B a (ho 1 2) (ho 1 1) hBC r t
    · exact actualStrip3_faces_avoid B a h12 (ho 2 2) (ho 1 2) r t
    · exact actualStrip4_faces_avoid B a (ho 2 0) (ho 2 2) hCA r t
    · exact actualStrip5_faces_avoid B a h20 (ho 0 0) (ho 2 0) r t
  · intro r t
    rw [realTriangleAffineMap_face_eq_segment]
    fin_cases r
    · exact h12 t
    · exact h02 t
    · exact h01 t

end ChenRanks
