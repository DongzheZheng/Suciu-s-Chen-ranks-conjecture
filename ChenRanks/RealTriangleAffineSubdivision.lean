import ChenRanks.SingularSquareTriangleGeometry
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

/-!
# Genuine affine subtriangles in the real standard triangle

The true barycentric combination of three original standard-triangle
points gives an actual continuous map into that same triangle. A
strict coordinate bound on its actual vertices is inherited by every
image point, and therefore excludes a genuine selected puncture. The
native face formulas retain their actual ordered edge orientations.
No subdivision, covering, or puncture detector is assumed.
-/

noncomputable section

open scoped BigOperators
open unitInterval

namespace ChenRanks

/-- The actual affine subtriangle with the actual ordered vertices v. -/
def realTriangleAffineMap (v : Fin 3 → stdSimplex ℝ (Fin 3)) :
    C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 3)) where
  toFun q := ⟨fun j => ∑ i : Fin 3, q i * v i j, by
    constructor
    · intro j
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (q.property.1 i) ((v i).property.1 j))
    · change (∑ j : Fin 3, ∑ i : Fin 3, q i * v i j) = 1
      rw [Finset.sum_comm]
      have hs : (∑ i : Fin 3, ∑ j : Fin 3, q i * v i j) =
          ∑ i : Fin 3, q i := by
        apply Finset.sum_congr rfl
        intro i _
        have hvSum : (∑ j : Fin 3, v i j) = 1 := by
          change (∑ j : Fin 3, (v i).val j) = 1
          exact (v i).property.2
        rw [← Finset.mul_sum, hvSum, mul_one]
      rw [hs]
      exact q.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact continuous_finset_sum _ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const)

@[simp] theorem realTriangleAffineMap_coordinate
    (v : Fin 3 → stdSimplex ℝ (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) (j : Fin 3) :
    realTriangleAffineMap v q j = ∑ i : Fin 3, q i * v i j := rfl

/-- The genuine barycentric map sends each native vertex to the
corresponding actual ordered vertex. -/
@[simp] theorem realTriangleAffineMap_vertex
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    realTriangleAffineMap v (stdSimplex.vertex i) = v i := by
  apply Subtype.ext
  funext j
  change (∑ l : Fin 3, (Pi.single i (1 : ℝ) : Fin 3 → ℝ) l * v l j) = v i j
  simp [Pi.single_apply]

/-- A strict actual vertex-coordinate bound holds on the entire
actual affine subtriangle, including its boundary. -/
theorem realTriangleAffineMap_coordinate_lt
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (j : Fin 3) (c : ℝ)
    (hv : ∀ i : Fin 3, v i j < c) (q : stdSimplex ℝ (Fin 3)) :
    realTriangleAffineMap v q j < c := by
  have hpos : ∃ i : Fin 3, 0 < q i := by
    by_contra h
    push Not at h
    have hs : (∑ i : Fin 3, q i) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => h i)
    change (∑ i : Fin 3, q.val i) ≤ 0 at hs
    rw [q.property.2] at hs
    linarith
  obtain ⟨i, hi⟩ := hpos
  rw [realTriangleAffineMap_coordinate]
  calc
    (∑ l : Fin 3, q l * v l j) < ∑ l : Fin 3, q l * c := by
      apply Finset.sum_lt_sum
      · intro l _
        exact mul_le_mul_of_nonneg_left (hv l).le (q.property.1 l)
      · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hv i) hi⟩
    _ = c := by
      have hqSum : (∑ l : Fin 3, q l) = 1 := by
        change (∑ l : Fin 3, q.val l) = 1
        exact q.property.2
      rw [← Finset.sum_mul, hqSum, one_mul]

/-- A strict original barycentric-coordinate bound genuinely excludes
the chosen original puncture from the whole actual subtriangle. -/
theorem realTriangleAffineMap_ne_of_coordinate_lt
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (p : stdSimplex ℝ (Fin 3))
    (j : Fin 3) (hv : ∀ i : Fin 3, v i j < p j)
    (q : stdSimplex ℝ (Fin 3)) : realTriangleAffineMap v q ≠ p := by
  intro heq
  have hlt := realTriangleAffineMap_coordinate_lt v j (p j) hv q
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- The true native face parametrization has the genuine ordered edge
weights, so different subtriangles can share literal singular edges. -/
theorem realTriangleAffineMap_face_coordinate
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (i : Fin 3) (t : I)
    (j : Fin 3) :
    realTriangleAffineMap v (SingularCohomology.realTriangleFacePath i t) j =
      (1 - (t : ℝ)) * v (i.succAbove 0) j +
        (t : ℝ) * v (i.succAbove 1) j := by
  rw [realTriangleAffineMap_coordinate]
  fin_cases i <;>
    simp [SingularCohomology.realTriangleFacePath_coordinate,
      Fin.sum_univ_succ, Fin.succAbove]

end ChenRanks
