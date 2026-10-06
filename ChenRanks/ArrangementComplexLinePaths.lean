import ChenRanks.ArrangementPathUniformNeighborhood

/-! Actual short affine-line paths in the original complement. The
avoidance condition is proved from the already constructed actual path
tube; no segment-in-complement or homotopy assumption is supplied. -/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- An actual original affine-line interpolation, with complex scalar
multiplication compatible with the original ambient vector space. -/
def actualComplexLinePoint (x y : Fin d → ℂ) (t : I) : Fin d → ℂ :=
  x + ((t : ℝ) : ℂ) • (y - x)

@[simp] theorem actualComplexLinePoint_zero (x y : Fin d → ℂ) :
    actualComplexLinePoint x y 0 = x := by
  change x + (0 : ℂ) • (y - x) = x
  rw [zero_smul, add_zero]

@[simp] theorem actualComplexLinePoint_one (x y : Fin d → ℂ) :
    actualComplexLinePoint x y 1 = y := by
  change x + (1 : ℂ) • (y - x) = y
  rw [one_smul, add_sub_cancel]

@[simp] theorem actualComplexLinePoint_self (x : Fin d → ℂ) (t : I) :
    actualComplexLinePoint x x t = x := by
  simp [actualComplexLinePoint]

/-- Exact metric distance along the actual affine segment. -/
theorem actualComplexLinePoint_dist_source (x y : Fin d → ℂ) (t : I) :
    dist (actualComplexLinePoint x y t) x = (t : ℝ) * dist y x := by
  rw [actualComplexLinePoint, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg t.property.1, dist_eq_norm]

/-- This elementary bound is valid even for equal endpoints and for
any reference center. It suffices for fixed-endpoint straightening. -/
theorem actualComplexLinePoint_dist_center_le (x y c : Fin d → ℂ) (t : I) :
    dist (actualComplexLinePoint x y t) c ≤ dist y c + 2 * dist x c := by
  calc
    dist (actualComplexLinePoint x y t) c ≤
        dist (actualComplexLinePoint x y t) x + dist x c := dist_triangle _ _ _
    _ = (t : ℝ) * dist y x + dist x c := by
      rw [actualComplexLinePoint_dist_source]
    _ ≤ dist y x + dist x c := by
      have hm := mul_le_of_le_one_left
        (dist_nonneg : (0 : ℝ) ≤ dist y x) t.property.2
      linarith
    _ ≤ dist y c + 2 * dist x c := by
      have h := dist_triangle y c x
      rw [dist_comm c x] at h
      linarith

/-- The actual straight segment from a genuine path point to a genuine
nearby complement point lies in the same original complement. -/
def segmentInActualPathTube (γ : C(I, A.Complement)) (a : I)
    (y : A.Complement)
    (hy : dist y.val (γ a).val < A.actualPathAvoidanceRadius γ) :
    Path (γ a) y where
  toFun t := ⟨actualComplexLinePoint (γ a).val y.val t, by
    apply A.actualPathAvoidanceRadius_avoids γ a
    rw [actualComplexLinePoint_dist_source]
    exact (mul_le_of_le_one_left dist_nonneg t.property.2).trans_lt hy⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold actualComplexLinePoint
    fun_prop
  source' := by
    apply Subtype.ext
    exact actualComplexLinePoint_zero _ _
  target' := by
    apply Subtype.ext
    exact actualComplexLinePoint_one _ _

/-- The actual segment stays within the genuine endpoint distance of
its original path point. -/
theorem segmentInActualPathTube_dist_le (γ : C(I, A.Complement)) (a : I)
    (y : A.Complement)
    (hy : dist y.val (γ a).val < A.actualPathAvoidanceRadius γ) (t : I) :
    dist (A.segmentInActualPathTube γ a y hy t).val (γ a).val ≤
      dist y.val (γ a).val := by
  change dist (actualComplexLinePoint (γ a).val y.val t) (γ a).val ≤ _
  rw [actualComplexLinePoint_dist_source]
  exact mul_le_of_le_one_left dist_nonneg t.property.2

end ChenRanks.AffineArrangement
