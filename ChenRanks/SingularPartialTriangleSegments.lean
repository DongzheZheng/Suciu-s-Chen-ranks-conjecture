import ChenRanks.SingularClosedCocyclePathReversal
import ChenRanks.RealTrianglePunctureFreeEdges

/-!
# Literal actual segment values and native partial-triangle boundaries

The value assigned to a segment is its original singular cochain value
whenever the whole genuine segment lies in U. Only such proved-safe
segments are used in the identities. Actual affine face equality and
the genuine native reversal triangle derive the boundary and signed
reversal formulas; neither is an integration axiom.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (V : Type) [TopologicalSpace V] (U : Set V)

def partialTriangleSegmentPath (F : C(stdSimplex ℝ (Fin 3), V))
    (a b : stdSimplex ℝ (Fin 3))
    (h : ∀ t : I, F (realTriangleSegmentPath a b t) ∈ U) : C(I, U) where
  toFun t := ⟨F (realTriangleSegmentPath a b t), h t⟩
  continuous_toFun :=
    (F.continuous.comp (realTriangleSegmentPath a b).continuous).subtype_mk h

variable (k : Type) [Field k]

def partialTriangleSegmentValue (β : cochains k U 1)
    (F : C(stdSimplex ℝ (Fin 3), V)) (a b : stdSimplex ℝ (Fin 3)) : k := by
  classical
  exact if h : ∀ t : I, F (realTriangleSegmentPath a b t) ∈ U then
    values k U 1 β (simplexOfPath U (partialTriangleSegmentPath V U F a b h)) else 0

theorem partialTriangleSegmentValue_of_safe (β : cochains k U 1)
    (F : C(stdSimplex ℝ (Fin 3), V)) (a b : stdSimplex ℝ (Fin 3))
    (h : ∀ t : I, F (realTriangleSegmentPath a b t) ∈ U) :
    partialTriangleSegmentValue V U k β F a b =
      values k U 1 β (simplexOfPath U (partialTriangleSegmentPath V U F a b h)) := by
  classical
  exact dif_pos h

theorem partialTriangleAffineFace_value_eq_segment
    (β : cochains k U 1) (F : C(stdSimplex ℝ (Fin 3), V))
    (v : Fin 3 → stdSimplex ℝ (Fin 3))
    (hF : ∀ (i : Fin 3) (t : I),
      F (realTriangleAffineMap v (realTriangleFacePath i t)) ∈ U)
    (i : Fin 3) :
    values k U 1 β (simplexOfPath U
      (partialTriangleFacePath V U (F.comp (realTriangleAffineMap v)) hF i)) =
      partialTriangleSegmentValue V U k β F (v (i.succAbove 0)) (v (i.succAbove 1)) := by
  have hs : ∀ t : I, F (realTriangleSegmentPath (v (i.succAbove 0)) (v (i.succAbove 1)) t) ∈ U := by
    intro t
    rw [← realTriangleAffineMap_face_eq_segment]
    exact hF i t
  rw [partialTriangleSegmentValue_of_safe V U k β F _ _ hs]
  have heq : partialTriangleFacePath V U (F.comp (realTriangleAffineMap v)) hF i =
      partialTriangleSegmentPath V U F (v (i.succAbove 0)) (v (i.succAbove 1)) hs := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change F (realTriangleAffineMap v (realTriangleFacePath i t)) =
      F (realTriangleSegmentPath (v (i.succAbove 0)) (v (i.succAbove 1)) t)
    rw [realTriangleAffineMap_face_eq_segment]
  rw [heq]

theorem partialTriangleBoundaryValue_affineMap_eq_segments
    (β : cochains k U 1) (F : C(stdSimplex ℝ (Fin 3), V))
    (v : Fin 3 → stdSimplex ℝ (Fin 3))
    (hF : ∀ (i : Fin 3) (t : I),
      F (realTriangleAffineMap v (realTriangleFacePath i t)) ∈ U) :
    partialTriangleBoundaryValue V U k β (F.comp (realTriangleAffineMap v)) hF =
      partialTriangleSegmentValue V U k β F (v 0) (v 2) -
        partialTriangleSegmentValue V U k β F (v 0) (v 1) -
        partialTriangleSegmentValue V U k β F (v 1) (v 2) := by
  unfold partialTriangleBoundaryValue
  rw [partialTriangleAffineFace_value_eq_segment,
    partialTriangleAffineFace_value_eq_segment, partialTriangleAffineFace_value_eq_segment]
  simp [Fin.succAbove]

theorem realTriangleSegmentPath_reversal_point
    (a b : stdSimplex ℝ (Fin 3)) (t : I) :
    realTriangleSegmentPath a b (actualIntervalReversal t) = realTriangleSegmentPath b a t := by
  apply Subtype.ext
  funext j
  change realTriangleSegmentPath a b (actualIntervalReversal t) j = realTriangleSegmentPath b a t j
  rw [realTriangleSegmentPath_coordinate, realTriangleSegmentPath_coordinate]
  change (1 - (1 - (t : ℝ))) * a j + (1 - (t : ℝ)) * b j =
    (1 - (t : ℝ)) * b j + (t : ℝ) * a j
  ring

/-- Every proved-safe actual segment has the true signed reversed
value, derived from the original closed-cochain triangle relation. -/
theorem partialTriangleSegmentValue_reverse (β : cochains k U 1)
    (hβ : differential k U 1 β = 0) (F : C(stdSimplex ℝ (Fin 3), V))
    (a b : stdSimplex ℝ (Fin 3))
    (h : ∀ t : I, F (realTriangleSegmentPath a b t) ∈ U) :
    partialTriangleSegmentValue V U k β F b a = -partialTriangleSegmentValue V U k β F a b := by
  have hr : ∀ t : I, F (realTriangleSegmentPath b a t) ∈ U := by
    intro t
    rw [← realTriangleSegmentPath_reversal_point]
    exact h (actualIntervalReversal t)
  rw [partialTriangleSegmentValue_of_safe V U k β F a b h,
    partialTriangleSegmentValue_of_safe V U k β F b a hr]
  have heq : actualReversedContinuousPath (partialTriangleSegmentPath V U F a b h) =
      partialTriangleSegmentPath V U F b a hr := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change F (realTriangleSegmentPath a b (actualIntervalReversal t)) =
      F (realTriangleSegmentPath b a t)
    rw [realTriangleSegmentPath_reversal_point]
  simpa only [heq] using closedOne_reversed_path_value k U β hβ
    (partialTriangleSegmentPath V U F a b h)

end ChenRanks.SingularCohomology
