import ChenRanks.ArrangementTransverseMeridianFamilies

/-!
# A genuine small tube at one regular original hyperplane point

The radius is derived from the finite original equations. The first
homotopy preserves the distinguished equation exactly. The second
homotopy changes only its positive modulus inside a proved transverse
disk. No tube, regular lift, local loop detector, or meridian-generation
statement is an input.
-/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance singleHyperplaneInnerTubeDecidableEq : DecidableEq ι := Classical.decEq ι

/-- A normal vector is chosen from the original nonzero linear equation. -/
def innerTubeNormal (H : ι) : Fin d → ℂ :=
  (A.exists_actual_meridian_normal_vector H).choose

theorem innerTubeNormal_value (H : ι) : A.normal H (A.innerTubeNormal H) = 1 :=
  (A.exists_actual_meridian_normal_vector H).choose_spec

private def constantTransverseLift (H : ι) : C(I × ℂ, Fin d → ℂ) where
  toFun p := p.2 • A.innerTubeNormal H
  continuous_toFun := continuous_snd.smul continuous_const

private theorem constantTransverseLift_zero (H : ι) (t : I) :
    A.constantTransverseLift H (t, 0) = 0 := by
  exact zero_smul ℂ (A.innerTubeNormal H)

/-- An actual transverse disk centered at the supplied actual regular
point. Its radius is proved by compactness and the original equations. -/
def innerTubeMeridianDisk (H : ι) (w : A.HyperplaneRegularLocus H) :
    A.MeridianDisk H where
  center := w.val
  normalVector := A.innerTubeNormal H
  center_on := w.property.1
  center_avoids := w.property.2
  normal_value := A.innerTubeNormal_value H
  radius := A.actualTransverseFamilyRadius H (ContinuousMap.const I w)
    (A.constantTransverseLift H) (A.constantTransverseLift_zero H)
  radius_pos := A.actualTransverseFamilyRadius_pos H (ContinuousMap.const I w)
    (A.constantTransverseLift H) (A.constantTransverseLift_zero H)
  disk_avoids := by
    intro z hz K hKH
    exact A.actualTransverseFamilyRadius_avoids H (ContinuousMap.const I w)
      (A.constantTransverseLift H) (A.constantTransverseLift_zero H) 0 z hz K hKH

/-- The true projection onto the actual normal line through w. -/
def innerTubeProjection (H : ι) (w : A.HyperplaneRegularLocus H)
    (x : Fin d → ℂ) : Fin d → ℂ :=
  w.val + (A.normal H x - A.offset H) • A.innerTubeNormal H

/-- The interpolation kills the tangential component and keeps the
original distinguished equation constant. -/
def innerTubeAmbientInterpolation (H : ι) (w : A.HyperplaneRegularLocus H)
    (s : I) (x : Fin d → ℂ) : Fin d → ℂ :=
  x + ((s : ℝ) : ℂ) • (A.innerTubeProjection H w x - x)

theorem innerTubeAmbientInterpolation_equation (H : ι)
    (w : A.HyperplaneRegularLocus H) (s : I) (x : Fin d → ℂ) :
    A.normal H (A.innerTubeAmbientInterpolation H w s x) = A.normal H x := by
  unfold innerTubeAmbientInterpolation innerTubeProjection
  rw [map_add, map_smul, map_sub, map_add, map_smul,
    w.property.1, A.innerTubeNormal_value H]
  simp only [smul_eq_mul]
  ring

theorem innerTubeProjection_center (H : ι) (w : A.HyperplaneRegularLocus H) :
    A.innerTubeProjection H w w.val = w.val := by
  simp [innerTubeProjection, w.property.1]

theorem innerTubeAmbientInterpolation_center (H : ι)
    (w : A.HyperplaneRegularLocus H) (s : I) :
    A.innerTubeAmbientInterpolation H w s w.val = w.val := by
  simp [innerTubeAmbientInterpolation, A.innerTubeProjection_center H w]

private theorem innerTubeAmbientInterpolation_continuous (H : ι)
    (w : A.HyperplaneRegularLocus H) :
    Continuous (fun p : I × (Fin d → ℂ) => A.innerTubeAmbientInterpolation H w p.1 p.2) := by
  unfold innerTubeAmbientInterpolation innerTubeProjection
  have hn := (A.normal H).continuous_of_finiteDimensional
  have hproj : Continuous (fun p : I × (Fin d → ℂ) =>
      w.val + (A.normal H p.2 - A.offset H) • A.innerTubeNormal H) :=
    continuous_const.add (((hn.comp continuous_snd).sub continuous_const).smul
      continuous_const)
  exact continuous_snd.add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).smul
      (hproj.sub continuous_snd))

/-- A positive actual ambient radius works simultaneously for the
entire interpolation and every other original hyperplane. -/
theorem exists_actual_innerTube_radius (H : ι) (w : A.HyperplaneRegularLocus H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (s : I) (x : Fin d → ℂ), dist x w.val < ε →
      ‖A.normal H x - A.offset H‖ < (A.innerTubeMeridianDisk H w).radius ∧
      ∀ K : ι, K ≠ H →
        A.normal K (A.innerTubeAmbientInterpolation H w s x) ≠ A.offset K := by
  let U : Set (I × (Fin d → ℂ)) :=
    {p | ‖A.normal H p.2 - A.offset H‖ < (A.innerTubeMeridianDisk H w).radius} ∩
      ⋂ K : {K : ι // K ≠ H},
        {p | A.normal K.val (A.innerTubeAmbientInterpolation H w p.1 p.2) ≠ A.offset K.val}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt (((A.normal H).continuous_of_finiteDimensional.comp
        continuous_snd).sub continuous_const).norm continuous_const
    · apply isOpen_iInter_of_finite
      intro K
      exact isOpen_ne_fun ((A.normal K.val).continuous_of_finiteDimensional.comp
        (A.innerTubeAmbientInterpolation_continuous H w)) continuous_const
  let c : I → I × (Fin d → ℂ) := fun s => (s, w.val)
  have hc : Continuous c := continuous_id.prodMk continuous_const
  have hKU : Set.range c ⊆ U := by
    rintro _ ⟨s, rfl⟩
    constructor
    · change ‖A.normal H w.val - A.offset H‖ < _
      rw [w.property.1, sub_self, norm_zero]
      exact (A.innerTubeMeridianDisk H w).radius_pos
    · apply Set.mem_iInter.mpr
      intro K
      change A.normal K.val (A.innerTubeAmbientInterpolation H w s w.val) ≠ _
      rw [A.innerTubeAmbientInterpolation_center H w s]
      exact w.property.2 K.val K.property
  obtain ⟨ε, hε, hεU⟩ := (isCompact_range hc).exists_thickening_subset_open hU hKU
  refine ⟨ε, hε, ?_⟩
  intro s x hx
  have hd : dist (s, x) (c s) < ε := by
    simpa only [c, dist_prod_same_left] using hx
  have hp := hεU (Metric.mem_thickening_iff.mpr ⟨c s, ⟨s, rfl⟩, hd⟩)
  exact ⟨hp.1, fun K hKH => Set.mem_iInter.mp hp.2 ⟨K, hKH⟩⟩

/-- The radius is selected from that proved original finite-equation theorem. -/
def actualInnerTubeRadius (H : ι) (w : A.HyperplaneRegularLocus H) : ℝ :=
  (A.exists_actual_innerTube_radius H w).choose

theorem actualInnerTubeRadius_pos (H : ι) (w : A.HyperplaneRegularLocus H) :
    0 < A.actualInnerTubeRadius H w :=
  (A.exists_actual_innerTube_radius H w).choose_spec.1

theorem actualInnerTubeRadius_properties (H : ι) (w : A.HyperplaneRegularLocus H)
    (s : I) (x : Fin d → ℂ) (hx : dist x w.val < A.actualInnerTubeRadius H w) :
    ‖A.normal H x - A.offset H‖ < (A.innerTubeMeridianDisk H w).radius ∧
      ∀ K : ι, K ≠ H →
        A.normal K (A.innerTubeAmbientInterpolation H w s x) ≠ A.offset K :=
  (A.exists_actual_innerTube_radius H w).choose_spec.2 s x hx

/-- Actual affine contraction of a nearby original path inside the
same original complement. The circle parameter is the first coordinate. -/
def innerTubeRetractionHomotopy (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) :
    C(I × I, A.Complement) where
  toFun p := ⟨A.innerTubeAmbientInterpolation H w p.2 (γ p.1).val, by
    intro K
    by_cases hKH : K = H
    · subst K
      rw [A.innerTubeAmbientInterpolation_equation H w]
      exact (γ p.1).property H
    · exact (A.actualInnerTubeRadius_properties H w p.2 (γ p.1).val
        (hnear p.1)).2 K hKH⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (A.innerTubeAmbientInterpolation_continuous H w).comp
      (continuous_snd.prodMk
        (continuous_subtype_val.comp (γ.continuous.comp continuous_fst)))

theorem innerTubeRetractionHomotopy_zero (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) (t : I) :
    A.innerTubeRetractionHomotopy H w γ hnear (t, 0) = γ t := by
  apply Subtype.ext
  change (γ t).val + (0 : ℂ) • _ = (γ t).val
  rw [zero_smul, add_zero]

theorem innerTubeRetractionHomotopy_one (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) (t : I) :
    (A.innerTubeRetractionHomotopy H w γ hnear (t, 1)).val =
      A.innerTubeProjection H w (γ t).val := by
  change (γ t).val + (1 : ℂ) • (_ - (γ t).val) = _
  rw [one_smul, add_sub_cancel]

theorem innerTubeRetractionHomotopy_periodic (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w)
    (hclosed : γ 0 = γ 1) (s : I) :
    A.innerTubeRetractionHomotopy H w γ hnear (1, s) =
      A.innerTubeRetractionHomotopy H w γ hnear (0, s) := by
  apply Subtype.ext
  change A.innerTubeAmbientInterpolation H w s (γ 1).val =
    A.innerTubeAmbientInterpolation H w s (γ 0).val
  rw [hclosed]

private def positiveRadiusInterpolation (r a : ℝ) (s : I) : ℝ :=
  (1 - (s : ℝ)) * a + (s : ℝ) * r

private theorem positiveRadiusInterpolation_pos (r a : ℝ) (hr : 0 < r)
    (ha : 0 < a) (s : I) : 0 < positiveRadiusInterpolation r a s := by
  unfold positiveRadiusInterpolation
  by_cases hs : (s : ℝ) = 1
  · simp only [hs, sub_self, zero_mul, one_mul, zero_add]
    exact hr
  · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 hs
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hslt) ha)
      (mul_nonneg s.property.1 hr.le)

private theorem positiveRadiusInterpolation_le (r a : ℝ) (ha : a ≤ r) (s : I) :
    positiveRadiusInterpolation r a s ≤ r := by
  unfold positiveRadiusInterpolation
  have h := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr s.property.2)
  linarith

private theorem nonzeroComplex_norm_mul_phase (z : ChenRanks.NonzeroComplex) :
    (‖(z : ℂ)‖ : ℂ) * (ChenRanks.nonzeroComplexCircleMap z : ℂ) = (z : ℂ) := by
  change (‖(z : ℂ)‖ : ℂ) * Complex.exp (Complex.arg (z : ℂ) * Complex.I) = (z : ℂ)
  exact Complex.norm_mul_exp_arg_mul_I (z : ℂ)

/-- Actual radial homotopy in the constructed transverse disk. Its
modulus stays positive and at most the proved disk radius. -/
def innerTubeRadialHomotopy (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) :
    C(I × I, A.Complement) where
  toFun p :=
    let z := A.equationComplementNonzeroComplexMap H (γ p.1)
    let ρ := positiveRadiusInterpolation (A.innerTubeMeridianDisk H w).radius
      ‖(z : ℂ)‖ p.2
    let u := ChenRanks.nonzeroComplexCircleMap z
    ⟨w.val + ((ρ : ℂ) * (u : ℂ)) • A.innerTubeNormal H, by
      have hρ : 0 < ρ := positiveRadiusInterpolation_pos _ _
        (A.innerTubeMeridianDisk H w).radius_pos (norm_pos_iff.mpr z.property) p.2
      have hρle : ρ ≤ (A.innerTubeMeridianDisk H w).radius := by
        apply positiveRadiusInterpolation_le
        exact (A.actualInnerTubeRadius_properties H w 0 (γ p.1).val (hnear p.1)).1.le
      intro K
      by_cases hKH : K = H
      · subst K
        rw [map_add, map_smul, w.property.1, A.innerTubeNormal_value H,
          smul_eq_mul, mul_one]
        intro heq
        have hz : (ρ : ℂ) * (u : ℂ) = 0 :=
          add_left_cancel (heq.trans (add_zero (A.offset H)).symm)
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') u.coe_ne_zero hz
      · apply (A.innerTubeMeridianDisk H w).disk_avoids _ _ K hKH
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
          abs_of_pos hρ, mul_one]
        exact hρle⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold positiveRadiusInterpolation
    have hz : Continuous (fun p : I × I =>
        A.equationComplementNonzeroComplexMap H (γ p.1)) :=
      (A.equationComplementNonzeroComplexMap H).continuous.comp
      (γ.continuous.comp continuous_fst)
    have hu := continuous_subtype_val.comp
      (ChenRanks.nonzeroComplexCircleMap.continuous.comp hz)
    have hnorm := (continuous_subtype_val.comp hz).norm
    have hρ : Continuous (fun p : I × I =>
        (((1 - (p.2 : ℝ)) *
          ‖(A.equationComplementNonzeroComplexMap H (γ p.1) : ℂ)‖ +
            (p.2 : ℝ) * (A.innerTubeMeridianDisk H w).radius : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul hnorm).add
          ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
    exact continuous_const.add ((hρ.mul hu).smul continuous_const)

theorem innerTubeRadialHomotopy_zero (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) (t : I) :
    A.innerTubeRadialHomotopy H w γ hnear (t, 0) =
      A.innerTubeRetractionHomotopy H w γ hnear (t, 1) := by
  apply Subtype.ext
  rw [A.innerTubeRetractionHomotopy_one H w γ hnear t]
  change w.val +
    (((positiveRadiusInterpolation _ ‖(A.equationComplementNonzeroComplexMap H (γ t) : ℂ)‖
        0 : ℝ) : ℂ) *
      (ChenRanks.nonzeroComplexCircleMap (A.equationComplementNonzeroComplexMap H (γ t)) : ℂ)) •
      A.innerTubeNormal H = A.innerTubeProjection H w (γ t).val
  simp only [positiveRadiusInterpolation, Set.Icc.coe_zero,
    sub_zero, one_mul, zero_mul, add_zero]
  rw [nonzeroComplex_norm_mul_phase]
  rfl

theorem innerTubeRadialHomotopy_one (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w) (t : I) :
    A.innerTubeRadialHomotopy H w γ hnear (t, 1) =
      A.meridianDiskCircleMap H (A.innerTubeMeridianDisk H w)
        (A.equationComplementCircleMap H (γ t)) := by
  apply Subtype.ext
  change w.val +
    (((positiveRadiusInterpolation (A.innerTubeMeridianDisk H w).radius
        ‖(A.equationComplementNonzeroComplexMap H (γ t) : ℂ)‖ 1 : ℝ) : ℂ) *
      (ChenRanks.nonzeroComplexCircleMap
        (A.equationComplementNonzeroComplexMap H (γ t)) : ℂ)) •
      A.innerTubeNormal H = _
  simp only [positiveRadiusInterpolation, Set.Icc.coe_one,
    sub_self, zero_mul, one_mul, zero_add]
  rfl

theorem innerTubeRadialHomotopy_periodic (H : ι) (w : A.HyperplaneRegularLocus H)
    (γ : C(I, A.Complement))
    (hnear : ∀ t : I, dist (γ t).val w.val < A.actualInnerTubeRadius H w)
    (hclosed : γ 0 = γ 1) (s : I) :
    A.innerTubeRadialHomotopy H w γ hnear (1, s) =
      A.innerTubeRadialHomotopy H w γ hnear (0, s) := by
  apply Subtype.ext
  change w.val + _ • A.innerTubeNormal H = w.val + _ • A.innerTubeNormal H
  rw [hclosed]

end ChenRanks.AffineArrangement
