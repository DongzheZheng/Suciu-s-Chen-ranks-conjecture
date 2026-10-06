import ChenRanks.RealTriangleAffineInjectivity
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-!
# Actual metric control of the genuine inner triangle

The third barycentric coordinate is reconstructed from the first two.
Consequently the actual standard-simplex metric is bounded by twice
the actual plane-coordinate distance. Genuine barycentric convex
combinations keep every actual inner-triangle point close to p, and
the original continuous map then keeps its entire image in any
specified actual neighborhood of its original value at p.
-/

noncomputable section

namespace ChenRanks

theorem complexTriangleCoordinate_dist_le (x y : ℂ) (i : Fin 3) :
    |complexTriangleCoordinate x i - complexTriangleCoordinate y i| ≤ 2 * ‖x - y‖ := by
  have hnorm : 0 ≤ ‖x - y‖ := norm_nonneg _
  fin_cases i
  · change |x.re - y.re| ≤ 2 * ‖x - y‖
    have h := Complex.abs_re_le_norm (x - y)
    rw [Complex.sub_re] at h
    linarith
  · change |x.im - y.im| ≤ 2 * ‖x - y‖
    have h := Complex.abs_im_le_norm (x - y)
    rw [Complex.sub_im] at h
    linarith
  · change |(1 - x.re - x.im) - (1 - y.re - y.im)| ≤ 2 * ‖x - y‖
    have heq : (1 - x.re - x.im) - (1 - y.re - y.im) =
        -((x - y).re + (x - y).im) := by
      rw [Complex.sub_re, Complex.sub_im]
      ring
    rw [heq, abs_neg]
    calc
      |(x - y).re + (x - y).im| ≤ |(x - y).re| + |(x - y).im| := abs_add_le _ _
      _ ≤ ‖x - y‖ + ‖x - y‖ :=
        add_le_add (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
      _ = 2 * ‖x - y‖ := by ring

theorem realTriangle_dist_le_twice_plane_dist
    (p q : stdSimplex ℝ (Fin 3)) :
    dist p q ≤ 2 * dist (realTrianglePlaneCoordinate p) (realTrianglePlaneCoordinate q) := by
  change dist p.val q.val ≤ _
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |p i - q i| ≤ _
  rw [← complexTriangleCoordinate_plane p i, ← complexTriangleCoordinate_plane q i]
  exact complexTriangleCoordinate_dist_le _ _ i

theorem realTrianglePlaneCoordinate_affineMap_difference
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (p q : stdSimplex ℝ (Fin 3)) :
    realTrianglePlaneCoordinate (realTriangleAffineMap v q) - realTrianglePlaneCoordinate p =
      ∑ i : Fin 3, q i • (realTrianglePlaneCoordinate (v i) - realTrianglePlaneCoordinate p) := by
  rw [realTrianglePlaneCoordinate_affineMap]
  have hs := q.property.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change q 0 + (q 1 + q 2) = 1 at hs
  have hsC : (q 0 : ℂ) + ((q 1 : ℂ) + (q 2 : ℂ)) = 1 := by exact_mod_cast hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (q 0 : ℂ) * realTrianglePlaneCoordinate (v 0) +
      (q 1 : ℂ) * realTrianglePlaneCoordinate (v 1) +
      (q 2 : ℂ) * realTrianglePlaneCoordinate (v 2) - realTrianglePlaneCoordinate p =
    (q 0 : ℂ) * (realTrianglePlaneCoordinate (v 0) - realTrianglePlaneCoordinate p) +
      ((q 1 : ℂ) * (realTrianglePlaneCoordinate (v 1) - realTrianglePlaneCoordinate p) +
        (q 2 : ℂ) * (realTrianglePlaneCoordinate (v 2) - realTrianglePlaneCoordinate p))
  linear_combination realTrianglePlaneCoordinate p * hsC

/-- Actual nearby vertices give an actual nearby whole inner triangle,
including all its actual edges. -/
theorem realTriangleAffineMap_plane_dist_lt
    (v : Fin 3 → stdSimplex ℝ (Fin 3)) (p : stdSimplex ℝ (Fin 3)) (ε : ℝ)
    (hv : ∀ i : Fin 3,
      dist (realTrianglePlaneCoordinate (v i)) (realTrianglePlaneCoordinate p) < ε)
    (q : stdSimplex ℝ (Fin 3)) :
    dist (realTrianglePlaneCoordinate (realTriangleAffineMap v q))
      (realTrianglePlaneCoordinate p) < ε := by
  have hpos : ∃ i : Fin 3, 0 < q i := by
    by_contra h
    push Not at h
    have hs : (∑ i : Fin 3, q i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    change (∑ i : Fin 3, q.val i) ≤ 0 at hs
    rw [q.property.2] at hs
    linarith
  obtain ⟨i, hi⟩ := hpos
  rw [dist_eq_norm, realTrianglePlaneCoordinate_affineMap_difference]
  calc
    ‖∑ l : Fin 3, q l • (realTrianglePlaneCoordinate (v l) - realTrianglePlaneCoordinate p)‖ ≤
        ∑ l : Fin 3, ‖q l • (realTrianglePlaneCoordinate (v l) - realTrianglePlaneCoordinate p)‖ :=
      norm_sum_le _ _
    _ = ∑ l : Fin 3, q l * ‖realTrianglePlaneCoordinate (v l) - realTrianglePlaneCoordinate p‖ := by
      apply Finset.sum_congr rfl
      intro l _
      change ‖(q l : ℂ) * (realTrianglePlaneCoordinate (v l) - realTrianglePlaneCoordinate p)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      change |q l| * ‖realTrianglePlaneCoordinate (v l) - realTrianglePlaneCoordinate p‖ = _
      have hq : |q l| = q l := abs_of_nonneg (show 0 ≤ q l from q.property.1 l)
      rw [hq]
    _ < ∑ l : Fin 3, q l * ε := by
      apply Finset.sum_lt_sum
      · intro l _
        apply mul_le_mul_of_nonneg_left _ (q.property.1 l)
        exact (show ‖realTrianglePlaneCoordinate (v l) - realTrianglePlaneCoordinate p‖ < ε
          from by simpa only [dist_eq_norm] using hv l).le
      · refine ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left ?_ hi⟩
        simpa only [dist_eq_norm] using hv i
    _ = ε := by
      have hsum : (∑ l : Fin 3, q l) = 1 := by
        change (∑ l : Fin 3, q.val l) = 1
        exact q.property.2
      rw [← Finset.sum_mul, hsum, one_mul]

/-- The radius controlling the entire genuine inner triangle is
derived from continuity of the original actual map at the chosen p. -/
theorem exists_planeRadius_controlling_actual_innerTriangle
    {V : Type*} [PseudoMetricSpace V] (F : C(stdSimplex ℝ (Fin 3), V))
    (p : stdSimplex ℝ (Fin 3)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Fin 3 → stdSimplex ℝ (Fin 3),
      (∀ i : Fin 3,
        dist (realTrianglePlaneCoordinate (v i)) (realTrianglePlaneCoordinate p) < δ) →
      ∀ q : stdSimplex ℝ (Fin 3), dist (F (realTriangleAffineMap v q)) (F p) < ε := by
  obtain ⟨η, hη, hcontrol⟩ :=
    Metric.continuousAt_iff.mp F.continuous.continuousAt ε hε
  refine ⟨η / 3, by positivity, ?_⟩
  intro v hv q
  apply hcontrol
  have hplane := realTriangleAffineMap_plane_dist_lt v p (η / 3) hv q
  have hmetric := realTriangle_dist_le_twice_plane_dist (realTriangleAffineMap v q) p
  nlinarith

end ChenRanks
