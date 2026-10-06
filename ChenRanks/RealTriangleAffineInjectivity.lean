import ChenRanks.RealTrianglePlaneCoordinates
import ChenRanks.RealTriangleAffineSubdivision
import ChenRanks.RealFanTriangleFiniteZeros
import Mathlib.Tactic

/-!
# Actual injectivity of the genuine affine subtriangle maps

The actual plane coordinate of the true barycentric map is the actual
three-vertex affine equation. Real linear independence therefore gives
true injectivity. For boundary-vertex strips, a positive opposite
barycentric coordinate proves the needed independence directly.
-/

noncomputable section

namespace ChenRanks

theorem singleton_span_nonmembership_symmetric {V : Type*}
    [AddCommGroup V] [Module ℝ V] (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span ℝ ({u} : Set V)) :
    u ∉ Submodule.span ℝ ({v} : Set V) := by
  intro huS
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp huS
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, zero_smul] at ht
    exact hu ht.symm
  apply hv
  have huMem : u ∈ Submodule.span ℝ ({u} : Set V) :=
    Submodule.mem_span_singleton_self u
  have hvMem := (Submodule.span ℝ ({u} : Set V)).smul_mem t⁻¹ huMem
  have heq : t⁻¹ • u = v := by
    rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rwa [heq] at hvMem

theorem singleton_span_nonmembership_shift_origin {V : Type*}
    [AddCommGroup V] [Module ℝ V] (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span ℝ ({u} : Set V)) :
    -v ∉ Submodule.span ℝ ({u - v} : Set V) := by
  intro h
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
  have hzero : t • u + (1 - t) • v = 0 := by
    calc
      t • u + (1 - t) • v = t • (u - v) + v := by
        rw [sub_smul, one_smul, smul_sub]
        abel
      _ = -v + v := by rw [ht]
      _ = 0 := neg_add_cancel v
  have hc := real_two_term_coefficients_eq_zero u v hu hv t (1 - t) hzero
  linarith [hc.1, hc.2]

theorem realTrianglePlaneCoordinate_affineMap
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (q : stdSimplex ℝ (Fin 3)) :
    realTrianglePlaneCoordinate (realTriangleAffineMap v q) =
      realFanTriangleEquation (realTrianglePlaneCoordinate (v 1))
        (realTrianglePlaneCoordinate (v 2)) (realTrianglePlaneCoordinate (v 0)) q := by
  have hRe (p : stdSimplex ℝ (Fin 3)) : (realTrianglePlaneCoordinate p).re = p 0 := by
    simp [realTrianglePlaneCoordinate]
  have hIm (p : stdSimplex ℝ (Fin 3)) : (realTrianglePlaneCoordinate p).im = p 1 := by
    simp [realTrianglePlaneCoordinate]
  apply Complex.ext
  · simp only [realFanTriangleEquation, Complex.add_re, Complex.smul_re, smul_eq_mul, hRe]
    change realTriangleAffineMap v q 0 =
      q 0 * v 0 0 + q 1 * v 1 0 + q 2 * v 2 0
    rw [realTriangleAffineMap_coordinate]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change q 0 * v 0 0 + (q 1 * v 1 0 + q 2 * v 2 0) = _
    ring
  · simp only [realFanTriangleEquation, Complex.add_im, Complex.smul_im, smul_eq_mul, hIm]
    change realTriangleAffineMap v q 1 =
      q 0 * v 0 1 + q 1 * v 1 1 + q 2 * v 2 1
    rw [realTriangleAffineMap_coordinate]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change q 0 * v 0 1 + (q 1 * v 1 1 + q 2 * v 2 1) = _
    ring

/-- The actual affine map is injective whenever its actual two
direction vectors are nonzero and independent in the real plane. -/
theorem realTriangleAffineMap_injective_of_ordered_noncollinearity
    (v : Fin 3 → stdSimplex ℝ (Fin 3))
    (h₀ : realTrianglePlaneCoordinate (v 0) ≠ realTrianglePlaneCoordinate (v 1))
    (h₂ : realTrianglePlaneCoordinate (v 2) - realTrianglePlaneCoordinate (v 1) ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate (v 0) -
        realTrianglePlaneCoordinate (v 1)} : Set ℂ)) :
    Function.Injective (realTriangleAffineMap v) := by
  have h₂0 : realTrianglePlaneCoordinate (v 2) ≠ realTrianglePlaneCoordinate (v 1) := by
    intro h
    apply h₂
    rw [h, sub_self]
    exact Submodule.zero_mem _
  have h₀S := singleton_span_nonmembership_symmetric
    (realTrianglePlaneCoordinate (v 0) - realTrianglePlaneCoordinate (v 1))
    (realTrianglePlaneCoordinate (v 2) - realTrianglePlaneCoordinate (v 1))
    (sub_ne_zero.mpr h₀) h₂
  intro p q hpq
  apply realFanTriangleEquation_injective _ _ _ h₂0 h₀S
  rw [← realTrianglePlaneCoordinate_affineMap, ← realTrianglePlaneCoordinate_affineMap, hpq]

/-- An actual positive opposite barycentric coordinate puts a point
off the genuine real line through the other two actual vertices. -/
theorem realTrianglePlaneCoordinate_off_opposite_vertex_line
    (a : stdSimplex ℝ (Fin 3)) (i j l : Fin 3)
    (ha : 0 < a i) (hij : i ≠ j) (hil : i ≠ l) :
    realTrianglePlaneCoordinate a - realTrianglePlaneCoordinate (stdSimplex.vertex j) ∉
      Submodule.span ℝ ({realTrianglePlaneCoordinate (stdSimplex.vertex l) -
        realTrianglePlaneCoordinate (stdSimplex.vertex j)} : Set ℂ) := by
  intro h
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
  have heq : realTrianglePlaneCoordinate a =
      (1 - t) • realTrianglePlaneCoordinate (stdSimplex.vertex j) +
        t • realTrianglePlaneCoordinate (stdSimplex.vertex l) := by
    calc
      realTrianglePlaneCoordinate a = realTrianglePlaneCoordinate (stdSimplex.vertex j) +
          t • (realTrianglePlaneCoordinate (stdSimplex.vertex l) -
            realTrianglePlaneCoordinate (stdSimplex.vertex j)) := by rw [ht]; abel
      _ = _ := by rw [sub_smul, one_smul, smul_sub]; abel
  have hc := congrArg (fun z : ℂ => complexTriangleCoordinate z i) heq
  dsimp only at hc
  rw [complexTriangleCoordinate_affine, complexTriangleCoordinate_plane,
    complexTriangleCoordinate_plane, complexTriangleCoordinate_plane] at hc
  have hj : (stdSimplex.vertex j : stdSimplex ℝ (Fin 3)) i = 0 := by
    simp [stdSimplex.vertex, Pi.single_apply, hij, Ne.symm hij]
  have hl : (stdSimplex.vertex l : stdSimplex ℝ (Fin 3)) i = 0 := by
    simp [stdSimplex.vertex, Pi.single_apply, hil, Ne.symm hil]
  rw [hj, hl, mul_zero, mul_zero, add_zero] at hc
  exact ha.ne' hc

theorem realTrianglePlaneCoordinate_ne_vertex_of_positive_coordinate
    (a : stdSimplex ℝ (Fin 3)) (i j : Fin 3) (ha : 0 < a i) (hij : i ≠ j) :
    realTrianglePlaneCoordinate a ≠ realTrianglePlaneCoordinate (stdSimplex.vertex j) := by
  intro h
  have hc := congrArg (fun z : ℂ => complexTriangleCoordinate z i) h
  dsimp only at hc
  rw [complexTriangleCoordinate_plane, complexTriangleCoordinate_plane] at hc
  have hj : (stdSimplex.vertex j : stdSimplex ℝ (Fin 3)) i = 0 := by
    simp [stdSimplex.vertex, Pi.single_apply, hij, Ne.symm hij]
  rw [hj] at hc
  exact ha.ne' hc

theorem realTrianglePlaneCoordinate_vertex_ne_vertex (i j : Fin 3) (hij : i ≠ j) :
    realTrianglePlaneCoordinate (stdSimplex.vertex i) ≠
      realTrianglePlaneCoordinate (stdSimplex.vertex j) := by
  apply realTrianglePlaneCoordinate_ne_vertex_of_positive_coordinate _ i j _ hij
  simp [stdSimplex.vertex]

end ChenRanks
