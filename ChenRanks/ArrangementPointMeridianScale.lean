import ChenRanks.ArrangementPointAvoidanceNeighborhood
import ChenRanks.ArrangementMeridianCircle
import Mathlib.Analysis.Normed.Module.Basic

/-!
# A genuine small scale for original localized meridians

The disk is constructed in the actual point-localized central
arrangement. Its explicit norm bound and the proved original finite
avoidance neighborhood give a genuine positive scale. The whole
circle-scaled localized meridian remains in that original neighborhood.
No small-cycle embedding or scale is assumed.
-/

noncomputable section

open unitInterval
namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The true explicit norm bound of the genuinely constructed localized disk. -/
def localizedMeridianVectorBound (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) : ℝ :=
  let m := (A.pointLocalizedArrangement x).actualMeridianDisk H
  ‖m.center‖ + m.radius * ‖m.normalVector‖

theorem localizedMeridianVectorBound_nonneg (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) : 0 ≤ A.localizedMeridianVectorBound x H := by
  let m := (A.pointLocalizedArrangement x).actualMeridianDisk H
  change 0 ≤ ‖m.center‖ + m.radius * ‖m.normalVector‖
  exact add_nonneg (norm_nonneg _) (mul_nonneg m.radius_pos.le (norm_nonneg _))

/-- Every point of the actual localized meridian obeys that actual norm bound. -/
theorem localizedMeridianPath_norm_le (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (s : I) :
    ‖((A.pointLocalizedArrangement x).meridianDiskPathMap H
      ((A.pointLocalizedArrangement x).actualMeridianDisk H) s).val‖ ≤
      A.localizedMeridianVectorBound x H := by
  let m := (A.pointLocalizedArrangement x).actualMeridianDisk H
  change ‖m.center + ((m.radius : ℂ) * (positiveUnitCircleTraversal s : ℂ)) • m.normalVector‖ ≤
    ‖m.center‖ + m.radius * ‖m.normalVector‖
  have hm : ‖((m.radius : ℂ) * (positiveUnitCircleTraversal s : ℂ)) • m.normalVector‖ =
      m.radius * ‖m.normalVector‖ := by
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Circle.norm_coe, abs_of_pos m.radius_pos, mul_one]
  exact (norm_add_le _ _).trans_eq (by rw [hm])

/-- The positive scale is computed from the original neighborhood and actual disk bound. -/
def actualPointMeridianScale (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) : ℝ :=
  A.actualPointAvoidanceRadius x / (2 * (A.localizedMeridianVectorBound x H + 1))

theorem actualPointMeridianScale_pos (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) :
    0 < A.actualPointMeridianScale x H := by
  unfold actualPointMeridianScale
  exact div_pos (A.actualPointAvoidanceRadius_pos x)
    (by have hb := A.localizedMeridianVectorBound_nonneg x H; positivity)

theorem actualPointMeridianScale_mul_bound_lt_radius
    (x : Fin d → ℂ) (H : A.PointLocalizedLabels x) :
    A.actualPointMeridianScale x H * A.localizedMeridianVectorBound x H <
      A.actualPointAvoidanceRadius x := by
  have hb := A.localizedMeridianVectorBound_nonneg x H
  have hr := A.actualPointAvoidanceRadius_pos x
  have hd : 0 < 2 * (A.localizedMeridianVectorBound x H + 1) := by positivity
  unfold actualPointMeridianScale
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hd).mpr
  nlinarith

/-- Every original scalar-circle multiple of the true localized meridian
lies in the genuine original avoidance ball after the constructed scale. -/
theorem scaledLocalizedMeridian_norm_lt_radius (x : Fin d → ℂ)
    (H : A.PointLocalizedLabels x) (u : Circle) (s : I) :
    ‖((A.actualPointMeridianScale x H : ℂ) * (u : ℂ)) •
      ((A.pointLocalizedArrangement x).meridianDiskPathMap H
        ((A.pointLocalizedArrangement x).actualMeridianDisk H) s).val‖ <
      A.actualPointAvoidanceRadius x := by
  rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
    abs_of_pos (A.actualPointMeridianScale_pos x H), mul_one]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (A.localizedMeridianPath_norm_le x H s)
      (A.actualPointMeridianScale_pos x H).le)
    (A.actualPointMeridianScale_mul_bound_lt_radius x H)

end ChenRanks.AffineArrangement
