import ChenRanks.TwicePuncturedPhaseGrid
import ChenRanks.ComplexPathWindingOutsideBound

/-!
# Genuine finite support of winding around the actual phase grid

The grid is the actual deleted grid of the two argument lifts. Its
intersection with every actual norm ball is proved finite using bounds
on the two actual integer coordinates. Compactness bounds each actual
closed path, and the proved genuine straight contraction kills winding
around every point outside that bound. Thus finite support follows from
the original geometry; it is not a premise on a prescribed integer table.

This constructs the actual finitely supported winding table and its
actual total. Concatenation, deck translation and the rectangle formula
are separate identities still to be proved.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The actual real-coordinate identification of the argument plane with ℂ. -/
def argumentPlaneComplexMap : C(ℝ × ℝ, ℂ) where
  toFun p := ⟨p.1, p.2⟩
  continuous_toFun := by
    have h : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    simpa only [Complex.mk_eq_add_mul_I] using h

theorem argumentPlaneComplexMap_injective : Function.Injective argumentPlaneComplexMap := by
  intro p q h
  apply Prod.ext
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

/-- The same actual deleted grid point in actual complex coordinates. -/
def windingPhaseGridComplexPoint (n : ℤ × ℤ) : ℂ :=
  argumentPlaneComplexMap (windingPhaseGridPoint n)

@[simp] theorem windingPhaseGridComplexPoint_re (n : ℤ × ℤ) :
    (windingPhaseGridComplexPoint n).re = Real.pi + (n.1 : ℝ) * (2 * Real.pi) := rfl

@[simp] theorem windingPhaseGridComplexPoint_im (n : ℤ × ℤ) :
    (windingPhaseGridComplexPoint n).im = Real.pi + (n.2 : ℝ) * (2 * Real.pi) := rfl

private theorem phaseGridCoordinate_bounds (R : ℝ) (N : ℕ)
    (hN : R + Real.pi < (N : ℝ) * (2 * Real.pi)) (m : ℤ)
    (hm : |Real.pi + (m : ℝ) * (2 * Real.pi)| ≤ R) :
    -(N : ℤ) ≤ m ∧ m ≤ (N : ℤ) := by
  have habs := abs_le.mp hm
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hlo : -(N : ℝ) ≤ (m : ℝ) := by
    by_contra h
    have hneg : (m : ℝ) + (N : ℝ) < 0 := by linarith
    have hmul := mul_neg_of_neg_of_pos hneg hperiod
    nlinarith [habs.1]
  have hhi : (m : ℝ) ≤ (N : ℝ) := by
    by_contra h
    have hpos : 0 < (m : ℝ) - (N : ℝ) := by linarith
    have hmul := mul_pos hpos hperiod
    nlinarith [habs.2, Real.pi_pos]
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- Every actual norm ball contains only finitely many actual grid indices. -/
theorem windingPhaseGridComplexPoint_norm_bounded_finite (R : ℝ) :
    {n : ℤ × ℤ | ‖windingPhaseGridComplexPoint n‖ ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + Real.pi) / (2 * Real.pi))
  have hN' : R + Real.pi < (N : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hN
  apply ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod
    (Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
  intro n hn
  have hre : |Real.pi + (n.1 : ℝ) * (2 * Real.pi)| ≤ R := by
    exact (Complex.abs_re_le_norm (windingPhaseGridComplexPoint n)).trans hn
  have him : |Real.pi + (n.2 : ℝ) * (2 * Real.pi)| ≤ R := by
    exact (Complex.abs_im_le_norm (windingPhaseGridComplexPoint n)).trans hn
  exact ⟨phaseGridCoordinate_bounds R N hN' n.1 hre,
    phaseGridCoordinate_bounds R N hN' n.2 him⟩

/-- Actual grid avoidance is preserved by the actual coordinate identification. -/
theorem argumentPlaneComplexPath_ne_gridPoint (θ : C(I, ℝ × ℝ))
    (havoid : ∀ t, θ t ∉ windingPhaseGrid) (n : ℤ × ℤ) (t : I) :
    argumentPlaneComplexMap (θ t) ≠ windingPhaseGridComplexPoint n := by
  intro h
  apply havoid t
  exact ⟨n, (argumentPlaneComplexMap_injective h).symm⟩

/-- The integer at each actual deleted grid point is its genuine
covering-space winding around the original actual path. -/
def phaseGridPathWindingValues (θ : C(I, ℝ × ℝ))
    (havoid : ∀ t, θ t ∉ windingPhaseGrid) : (ℤ × ℤ) → ℤ :=
  fun n => complexPathWindingAround (argumentPlaneComplexMap.comp θ)
    (windingPhaseGridComplexPoint n) (argumentPlaneComplexPath_ne_gridPoint θ havoid n)

/-- Compactness and the actual outside-bound contraction give genuine
finite support of the original closed path's puncture winding table. -/
theorem phaseGridPathWindingValues_support_finite (θ : C(I, ℝ × ℝ))
    (hclosed : θ 0 = θ 1) (havoid : ∀ t, θ t ∉ windingPhaseGrid) :
    (Function.support (phaseGridPathWindingValues θ havoid)).Finite := by
  let γ : C(I, ℂ) := argumentPlaneComplexMap.comp θ
  obtain ⟨R, hR⟩ := (isCompact_range γ.continuous.norm).bddAbove
  apply (windingPhaseGridComplexPoint_norm_bounded_finite R).subset
  intro n hn
  by_contra hbound
  have hout : R < ‖windingPhaseGridComplexPoint n‖ := lt_of_not_ge hbound
  have hnorm (t : I) : ‖γ t‖ < ‖windingPhaseGridComplexPoint n‖ :=
    (hR ⟨t, rfl⟩).trans_lt hout
  have hγ : γ 0 = γ 1 := congrArg argumentPlaneComplexMap hclosed
  have hz := complexPathWindingAround_eq_zero_of_norm_bound γ hγ
    (windingPhaseGridComplexPoint n) (argumentPlaneComplexPath_ne_gridPoint θ havoid n) hnorm
  exact hn hz

/-- The actual finitely supported winding table, with finite support
derived from compactness rather than imposed as input. -/
def phaseGridPathWindingFinsupp (θ : C(I, ℝ × ℝ))
    (hclosed : θ 0 = θ 1) (havoid : ∀ t, θ t ∉ windingPhaseGrid) : (ℤ × ℤ) →₀ ℤ :=
  Finsupp.ofSupportFinite (phaseGridPathWindingValues θ havoid)
    (phaseGridPathWindingValues_support_finite θ hclosed havoid)

@[simp] theorem phaseGridPathWindingFinsupp_apply (θ : C(I, ℝ × ℝ))
    (hclosed : θ 0 = θ 1) (havoid : ∀ t, θ t ∉ windingPhaseGrid) (n : ℤ × ℤ) :
    phaseGridPathWindingFinsupp θ hclosed havoid n = phaseGridPathWindingValues θ havoid n := rfl

/-- The actual finite total of the genuine puncture winding integers. -/
def phaseGridPathTotalWinding (θ : C(I, ℝ × ℝ))
    (hclosed : θ 0 = θ 1) (havoid : ∀ t, θ t ∉ windingPhaseGrid) : ℤ :=
  (phaseGridPathWindingFinsupp θ hclosed havoid).sum (fun _ v => v)

end ChenRanks
