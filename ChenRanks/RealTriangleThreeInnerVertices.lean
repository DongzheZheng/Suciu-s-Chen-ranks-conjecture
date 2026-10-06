import ChenRanks.RealTriangleInnerVertexConstruction
import ChenRanks.ArrangementSingleNormalRealLines
import ChenRanks.RealAffineEdgeAvoidance

/-!
# Actual three-vertex construction for the punctured-triangle induction

The three actual points are chosen successively in the true strict
barycentric sectors. Every actual puncture-to-vertex line and each
needed actual degeneracy line is included in finite affine avoidance.
Consequently all the new edges avoid the original finite puncture set,
and the three odd strips have genuinely noncollinear actual vertices.
No inner polygon, generic-position or edge-avoidance input is assumed.
-/

noncomputable section

namespace ChenRanks

def realTriangleInnerVertexProperties (p : stdSimplex ℝ (Fin 3))
    (ε : ℝ) (i : Fin 3) (q : stdSimplex ℝ (Fin 3)) : Prop :=
  (∀ j : Fin 3, 0 < q j) ∧ (∀ j : Fin 3, j ≠ i → q j < p j) ∧
    dist (realTrianglePlaneCoordinate q) (realTrianglePlaneCoordinate p) < ε

def realTriangleVertexOuterLineAvoidance (B : Set (stdSimplex ℝ (Fin 3)))
    (a : stdSimplex ℝ (Fin 3)) : Prop :=
  ∀ (q : stdSimplex ℝ (Fin 3)), q ∈ B → ∀ j : Fin 3,
    realTrianglePlaneCoordinate a - realTrianglePlaneCoordinate (stdSimplex.vertex j) ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate q -
        realTrianglePlaneCoordinate (stdSimplex.vertex j)} : Set ℂ)

def realTriangleVertexInnerLineAvoidance (B : Set (stdSimplex ℝ (Fin 3)))
    (a b : stdSimplex ℝ (Fin 3)) : Prop :=
  ∀ (q : stdSimplex ℝ (Fin 3)), q ∈ B →
    realTrianglePlaneCoordinate b - realTrianglePlaneCoordinate a ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate q - realTrianglePlaneCoordinate a} : Set ℂ)

/-- An actual finite family of real lines is automatically proper in
the actual complex plane; actual nearby sector avoidance constructs q. -/
theorem exists_realTriangleInnerVertex_avoiding_lines {ι : Type*} [Fintype ι]
    (c v : ι → ℂ) (p : stdSimplex ℝ (Fin 3))
    (hp : ∀ j : Fin 3, 0 < p j) (i : Fin 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : stdSimplex ℝ (Fin 3), realTriangleInnerVertexProperties p ε i q ∧
      ∀ l, realTrianglePlaneCoordinate q - c l ∉ Submodule.span ℝ ({v l} : Set ℂ) := by
  obtain ⟨q, hqpos, hqsector, hqdist, havoid⟩ :=
    exists_realTriangleInnerVertex_avoiding_finite_affine_subspaces
      (fun l => Submodule.span ℝ ({v l} : Set ℂ)) c
      (fun l => complex_real_singleton_span_ne_top (v l)) p hp i ε hε
  exact ⟨q, ⟨hqpos, hqsector, hqdist⟩, havoid⟩

/-- All three genuine inner vertices, all original-puncture line
avoidance, and all genuine odd-strip nondegeneracy are constructed
from the actual finite puncture set and the actual interior point. -/
theorem exists_realTriangle_three_inner_vertices
    (B : Set (stdSimplex ℝ (Fin 3))) (hB : B.Finite)
    (p : stdSimplex ℝ (Fin 3)) (hp : ∀ j : Fin 3, 0 < p j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a b c : stdSimplex ℝ (Fin 3),
      realTriangleInnerVertexProperties p ε 0 a ∧
      realTriangleInnerVertexProperties p ε 1 b ∧
      realTriangleInnerVertexProperties p ε 2 c ∧
      realTriangleVertexOuterLineAvoidance B a ∧
      realTriangleVertexOuterLineAvoidance B b ∧
      realTriangleVertexOuterLineAvoidance B c ∧
      realTriangleVertexInnerLineAvoidance B a b ∧
      realTriangleVertexInnerLineAvoidance B a c ∧
      realTriangleVertexInnerLineAvoidance B b c ∧
      (realTrianglePlaneCoordinate b - realTrianglePlaneCoordinate a ∉
        Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex 1) -
          realTrianglePlaneCoordinate a} : Set ℂ)) ∧
      (realTrianglePlaneCoordinate c - realTrianglePlaneCoordinate b ∉
        Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex 2) -
          realTrianglePlaneCoordinate b} : Set ℂ)) ∧
      (realTrianglePlaneCoordinate c - realTrianglePlaneCoordinate a ∉
        Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex 0) -
          realTrianglePlaneCoordinate a} : Set ℂ)) := by
  classical
  letI : Fintype B := hB.fintype
  let outerBase : B × Fin 3 → ℂ := fun l =>
    realTrianglePlaneCoordinate (stdSimplex.vertex l.2)
  let outerDirection : B × Fin 3 → ℂ := fun l =>
    realTrianglePlaneCoordinate l.1.val - outerBase l
  obtain ⟨a, ha, havoidA⟩ := exists_realTriangleInnerVertex_avoiding_lines
    outerBase outerDirection p hp 0 ε hε
  let cb : (B × Fin 3) ⊕ (B ⊕ Unit) → ℂ := fun l =>
    match l with
    | .inl l => outerBase l
    | .inr _ => realTrianglePlaneCoordinate a
  let vb : (B × Fin 3) ⊕ (B ⊕ Unit) → ℂ := fun l =>
    match l with
    | .inl l => outerDirection l
    | .inr (.inl q) => realTrianglePlaneCoordinate q.val - realTrianglePlaneCoordinate a
    | .inr (.inr _) => realTrianglePlaneCoordinate (stdSimplex.vertex 1) -
        realTrianglePlaneCoordinate a
  obtain ⟨b, hb, havoidB⟩ := exists_realTriangleInnerVertex_avoiding_lines cb vb p hp 1 ε hε
  let cc : (B × Fin 3) ⊕ (B ⊕ (B ⊕ Fin 2)) → ℂ := fun l =>
    match l with
    | .inl l => outerBase l
    | .inr (.inl _) => realTrianglePlaneCoordinate a
    | .inr (.inr (.inl _)) => realTrianglePlaneCoordinate b
    | .inr (.inr (.inr i)) => if i = 0 then realTrianglePlaneCoordinate b
        else realTrianglePlaneCoordinate a
  let vc : (B × Fin 3) ⊕ (B ⊕ (B ⊕ Fin 2)) → ℂ := fun l =>
    match l with
    | .inl l => outerDirection l
    | .inr (.inl q) => realTrianglePlaneCoordinate q.val - realTrianglePlaneCoordinate a
    | .inr (.inr (.inl q)) => realTrianglePlaneCoordinate q.val - realTrianglePlaneCoordinate b
    | .inr (.inr (.inr i)) => if i = 0 then
        realTrianglePlaneCoordinate (stdSimplex.vertex 2) - realTrianglePlaneCoordinate b
        else realTrianglePlaneCoordinate (stdSimplex.vertex 0) - realTrianglePlaneCoordinate a
  obtain ⟨c, hc, havoidC⟩ := exists_realTriangleInnerVertex_avoiding_lines cc vc p hp 2 ε hε
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq j
    exact havoidA (⟨q, hq⟩, j)
  · intro q hq j
    exact havoidB (.inl (⟨q, hq⟩, j))
  · intro q hq j
    exact havoidC (.inl (⟨q, hq⟩, j))
  · intro q hq
    exact havoidB (.inr (.inl ⟨q, hq⟩))
  · intro q hq
    exact havoidC (.inr (.inl ⟨q, hq⟩))
  · intro q hq
    exact havoidC (.inr (.inr (.inl ⟨q, hq⟩)))
  · exact havoidB (.inr (.inr ()))
  · simpa only [cc, vc, if_pos rfl] using
      havoidC (.inr (.inr (.inr 0)))
  · simpa only [cc, vc, show (1 : Fin 2) ≠ 0 by decide, if_false] using
      havoidC (.inr (.inr (.inr 1)))

end ChenRanks
