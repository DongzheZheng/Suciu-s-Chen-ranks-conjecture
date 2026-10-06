import ChenRanks.ArrangementTransverseMeridianFamilies
import ChenRanks.SingularPathFunctoriality

/-!
# Normalization of actual meridian cocycle values

All positive actual transverse disks for the same original hyperplane
have the same value under a genuine closed singular one-cochain. The
proof moves their centers along the actual regular hyperplane, linearly
interpolates their actual normalized normals, derives one uniform small
radius, and adjusts the two endpoint radii inside their actual disks.
No equality of meridian classes or spanning theorem is assumed.
-/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance meridianCocycleNormalizationDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Shrinking the radius retains all original equations and the actual disk. -/
def meridianDiskAtRadius (H : ι) (m : A.MeridianDisk H) (r : ℝ)
    (hr : 0 < r) (hle : r ≤ m.radius) : A.MeridianDisk H where
  center := m.center
  normalVector := m.normalVector
  center_on := m.center_on
  center_avoids := m.center_avoids
  normal_value := m.normal_value
  radius := r
  radius_pos := hr
  disk_avoids z hz K hKH := m.disk_avoids z (hz.trans hle) K hKH

private theorem interpolated_radius_pos (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (s : I) :
    0 < (1 - (s : ℝ)) * r + (s : ℝ) * R := by
  by_cases hs : (s : ℝ) = 1
  · simp only [hs, sub_self, zero_mul, one_mul, zero_add]
    exact hR
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne s.property.2 hs)) hr)
      (mul_nonneg s.property.1 hR.le)

private theorem interpolated_radius_le (r R : ℝ) (hle : r ≤ R) (s : I) :
    (1 - (s : ℝ)) * r + (s : ℝ) * R ≤ R := by
  have h := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr s.property.2)
  linarith

/-- A genuine free homotopy of actual circle boundaries inside one disk. -/
def meridianDiskRadiusHomotopy (H : ι) (m : A.MeridianDisk H) (r : ℝ)
    (hr : 0 < r) (hle : r ≤ m.radius) : C(I × I, A.Complement) where
  toFun p :=
    let ρ := (1 - (p.2 : ℝ)) * r + (p.2 : ℝ) * m.radius
    let u := positiveUnitCircleTraversal p.1
    ⟨m.center + ((ρ : ℂ) * (u : ℂ)) • m.normalVector, by
      have hρ : 0 < ρ := interpolated_radius_pos r m.radius hr m.radius_pos p.2
      intro K
      by_cases hKH : K = H
      · subst K
        rw [map_add, map_smul, m.center_on, m.normal_value, smul_eq_mul, mul_one]
        intro heq
        have hz : (ρ : ℂ) * (u : ℂ) = 0 :=
          add_left_cancel (heq.trans (add_zero (A.offset H)).symm)
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') u.coe_ne_zero hz
      · apply m.disk_avoids _ _ K hKH
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
          abs_of_pos hρ, mul_one]
        exact interpolated_radius_le r m.radius hle p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hρ : Continuous (fun p : I × I =>
        (((1 - (p.2 : ℝ)) * r + (p.2 : ℝ) * m.radius : ℝ) : ℂ)) := by
      fun_prop
    have hu : Continuous (fun p : I × I => (positiveUnitCircleTraversal p.1 : ℂ)) :=
      continuous_subtype_val.comp
      (positiveUnitCircleTraversal.continuous.comp continuous_fst)
    exact continuous_const.add ((hρ.mul hu).smul continuous_const)

theorem meridianDiskRadiusHomotopy_periodic (H : ι) (m : A.MeridianDisk H) (r : ℝ)
    (hr : 0 < r) (hle : r ≤ m.radius) (s : I) :
    A.meridianDiskRadiusHomotopy H m r hr hle (1, s) =
      A.meridianDiskRadiusHomotopy H m r hr hle (0, s) := by
  apply Subtype.ext
  change m.center + _ • m.normalVector = m.center + _ • m.normalVector
  rw [positiveUnitCircleTraversal_one, positiveUnitCircleTraversal_zero]

theorem squareBottomPath_meridianDiskRadiusHomotopy (H : ι) (m : A.MeridianDisk H)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ m.radius) :
    SingularCohomology.squareBottomPath A.Complement
        (A.meridianDiskRadiusHomotopy H m r hr hle) =
      A.meridianDiskPathMap H (A.meridianDiskAtRadius H m r hr hle) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change m.center +
    ((((1 - (0 : ℝ)) * r + (0 : ℝ) * m.radius : ℝ) : ℂ) *
      (positiveUnitCircleTraversal t : ℂ)) • m.normalVector = _
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  rfl

theorem squareTopPath_meridianDiskRadiusHomotopy (H : ι) (m : A.MeridianDisk H)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ m.radius) :
    SingularCohomology.squareTopPath A.Complement
        (A.meridianDiskRadiusHomotopy H m r hr hle) = A.meridianDiskPathMap H m := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change m.center +
    ((((1 - (1 : ℝ)) * r + (1 : ℝ) * m.radius : ℝ) : ℂ) *
      (positiveUnitCircleTraversal t : ℂ)) • m.normalVector = _
  simp only [sub_self, zero_mul, one_mul, zero_add]
  rfl

variable (k : Type) [Field k]

theorem meridianDiskAtRadius_closedCochain_value (H : ι) (m : A.MeridianDisk H)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ m.radius)
    (β : SingularCohomology.cochains k A.Complement 1)
    (hβ : SingularCohomology.differential k A.Complement 1 β = 0) :
    SingularCohomology.values k A.Complement 1 β
        (SingularCohomology.simplexOfPath A.Complement
          (A.meridianDiskPathMap H (A.meridianDiskAtRadius H m r hr hle))) =
      SingularCohomology.values k A.Complement 1 β
        (SingularCohomology.simplexOfPath A.Complement (A.meridianDiskPathMap H m)) := by
  have h := SingularCohomology.closedCochain_values_squareBottom_eq_top A.Complement k
    (A.meridianDiskRadiusHomotopy H m r hr hle)
    (A.meridianDiskRadiusHomotopy_periodic H m r hr hle) β hβ
  rwa [A.squareBottomPath_meridianDiskRadiusHomotopy,
    A.squareTopPath_meridianDiskRadiusHomotopy] at h

/-- Actual regular-path and normal interpolation transport the values
of any two actual positive meridians for the same original hyperplane. -/
theorem meridianDisk_closedCochain_values_eq (H : ι) (m₀ m₁ : A.MeridianDisk H)
    (β : SingularCohomology.cochains k A.Complement 1)
    (hβ : SingularCohomology.differential k A.Complement 1 β = 0) :
    SingularCohomology.values k A.Complement 1 β
        (SingularCohomology.simplexOfPath A.Complement (A.meridianDiskPathMap H m₀)) =
      SingularCohomology.values k A.Complement 1 β
        (SingularCohomology.simplexOfPath A.Complement (A.meridianDiskPathMap H m₁)) := by
  let w₀ : A.HyperplaneRegularLocus H := ⟨m₀.center, m₀.center_on, m₀.center_avoids⟩
  let w₁ : A.HyperplaneRegularLocus H := ⟨m₁.center, m₁.center_on, m₁.center_avoids⟩
  let γ := (A.hyperplaneRegularLocus_joined H w₀ w₁).somePath
  let n : C(I, Fin d → ℂ) :=
    ⟨fun s => (((1 - (s : ℝ) : ℝ) : ℂ)) • m₀.normalVector +
      (((s : ℝ) : ℂ)) • m₁.normalVector, by fun_prop⟩
  have hn : ∀ s : I, A.normal H (n s) = 1 := by
    intro s
    change A.normal H (((1 - (s : ℝ) : ℝ) : ℂ) • m₀.normalVector +
      ((s : ℝ) : ℂ) • m₁.normalVector) = 1
    rw [map_add, map_smul, map_smul, m₀.normal_value, m₁.normal_value]
    simp only [smul_eq_mul, mul_one, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hn₀ : n 0 = m₀.normalVector := by
    change (((1 - (0 : ℝ) : ℝ) : ℂ)) • m₀.normalVector +
      (((0 : ℝ) : ℂ)) • m₁.normalVector = m₀.normalVector
    simp
  have hn₁ : n 1 = m₁.normalVector := by
    change (((1 - (1 : ℝ) : ℝ) : ℂ)) • m₀.normalVector +
      (((1 : ℝ) : ℂ)) • m₁.normalVector = m₁.normalVector
    simp
  let T : C(I × ℂ, Fin d → ℂ) :=
    ⟨fun p => p.2 • n p.1, continuous_snd.smul (n.continuous.comp continuous_fst)⟩
  have hzero : ∀ s : I, T (s, 0) = 0 := by
    intro s
    exact zero_smul ℂ (n s)
  let R := A.actualTransverseFamilyRadius H γ.toContinuousMap T hzero
  let r := min R (min m₀.radius m₁.radius)
  have hr : 0 < r := lt_min (A.actualTransverseFamilyRadius_pos H γ.toContinuousMap T hzero)
    (lt_min m₀.radius_pos m₁.radius_pos)
  have hrR : r ≤ R := min_le_left _ _
  have hr₀ : r ≤ m₀.radius := (min_le_right _ _).trans (min_le_left _ _)
  have hr₁ : r ≤ m₁.radius := (min_le_right _ _).trans (min_le_right _ _)
  let F : C(I × I, A.Complement) := {
    toFun := fun p => ⟨(γ p.2).val +
        ((r : ℂ) * (positiveUnitCircleTraversal p.1 : ℂ)) • n p.2, by
      intro K
      by_cases hKH : K = H
      · subst K
        rw [map_add, map_smul, (γ p.2).property.1, hn, smul_eq_mul, mul_one]
        intro heq
        have hz : (r : ℂ) * (positiveUnitCircleTraversal p.1 : ℂ) = 0 :=
          add_left_cancel (heq.trans (add_zero (A.offset H)).symm)
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
          (positiveUnitCircleTraversal p.1).coe_ne_zero hz
      · apply A.actualTransverseFamilyRadius_avoids H γ.toContinuousMap T hzero p.2
          ((r : ℂ) * (positiveUnitCircleTraversal p.1 : ℂ)) _ K hKH
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
          abs_of_pos hr, mul_one]
        exact hrR⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp (γ.continuous.comp continuous_snd)).add
        ((continuous_const.mul (continuous_subtype_val.comp
          (positiveUnitCircleTraversal.continuous.comp continuous_fst))).smul
            (n.continuous.comp continuous_snd)) }
  have hperiodic : ∀ s : I, F (1, s) = F (0, s) := by
    intro s
    apply Subtype.ext
    change (γ s).val + _ • n s = (γ s).val + _ • n s
    rw [positiveUnitCircleTraversal_one, positiveUnitCircleTraversal_zero]
  have hbottom : SingularCohomology.squareBottomPath A.Complement F =
      A.meridianDiskPathMap H (A.meridianDiskAtRadius H m₀ r hr hr₀) := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change (γ 0).val + ((r : ℂ) * (positiveUnitCircleTraversal t : ℂ)) • n 0 = _
    rw [γ.source, hn₀]
    rfl
  have htop : SingularCohomology.squareTopPath A.Complement F =
      A.meridianDiskPathMap H (A.meridianDiskAtRadius H m₁ r hr hr₁) := by
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change (γ 1).val + ((r : ℂ) * (positiveUnitCircleTraversal t : ℂ)) • n 1 = _
    rw [γ.target, hn₁]
    rfl
  have h := SingularCohomology.closedCochain_values_squareBottom_eq_top
    A.Complement k F hperiodic β hβ
  rw [hbottom, htop] at h
  rw [A.meridianDiskAtRadius_closedCochain_value k H m₀ r hr hr₀ β hβ,
    A.meridianDiskAtRadius_closedCochain_value k H m₁ r hr hr₁ β hβ] at h
  exact h

end ChenRanks.AffineArrangement
