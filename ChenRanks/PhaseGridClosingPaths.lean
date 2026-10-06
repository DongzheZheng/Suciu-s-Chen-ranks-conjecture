import ChenRanks.PhaseGridWindingFiniteSupport

/-!
# Actual closing paths for lifted phase pairs

All paths live in the complement of the actual phase grid. The selected
principal-argument path is the straight radial path in the principal
square, whose only possible deleted corner is excluded by z+(1-z)=1.
The selected deck path is first vertical, then horizontal. This order
fixes the sign of the later rectangle winding computation.

The closing loop is constructed from the actual covering lift and its
proved endpoint integer pair. Its total winding exists by the proved
compactness argument. No concatenation formula, rectangle value, or
cup-product vanishing is assumed or asserted in this file.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The actual complement of the deleted argument grid. -/
abbrev PhaseGridComplement := {p : ℝ × ℝ // p ∉ windingPhaseGrid}

/-- The actual translation vector of an integer pair. -/
def windingPhaseDeckPoint (n : ℤ × ℤ) : ℝ × ℝ :=
  ((n.1 : ℝ) * (2 * Real.pi), (n.2 : ℝ) * (2 * Real.pi))

@[simp] theorem windingPhaseDeckPoint_zero : windingPhaseDeckPoint 0 = 0 := by
  ext <;> simp [windingPhaseDeckPoint]

/-- The grid-index translation is proved from the actual real coordinates. -/
theorem windingPhaseGridPoint_add_deck (m n : ℤ × ℤ) :
    windingPhaseGridPoint (m + n) = windingPhaseGridPoint m + windingPhaseDeckPoint n := by
  apply Prod.ext
  · change Real.pi + ((m.1 + n.1 : ℤ) : ℝ) * (2 * Real.pi) =
      (Real.pi + (m.1 : ℝ) * (2 * Real.pi)) + (n.1 : ℝ) * (2 * Real.pi)
    simp only [Int.cast_add]
    ring
  · change Real.pi + ((m.2 + n.2 : ℤ) : ℝ) * (2 * Real.pi) =
      (Real.pi + (m.2 : ℝ) * (2 * Real.pi)) + (n.2 : ℝ) * (2 * Real.pi)
    simp only [Int.cast_add]
    ring

/-- Actual deck translation preserves, and reflects, membership in the
actual deleted grid. -/
theorem add_windingPhaseDeckPoint_mem_grid_iff (p : ℝ × ℝ) (n : ℤ × ℤ) :
    p + windingPhaseDeckPoint n ∈ windingPhaseGrid ↔ p ∈ windingPhaseGrid := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m - n, ?_⟩
    apply add_right_cancel
    calc
      windingPhaseGridPoint (m - n) + windingPhaseDeckPoint n =
          windingPhaseGridPoint ((m - n) + n) :=
        (windingPhaseGridPoint_add_deck (m - n) n).symm
      _ = windingPhaseGridPoint m := by rw [sub_add_cancel]
      _ = p + windingPhaseDeckPoint n := hm
  · rintro ⟨m, hm⟩
    refine ⟨m + n, ?_⟩
    rw [windingPhaseGridPoint_add_deck, hm]

private theorem windingPhaseCutPoint_ne_one : windingPhaseCutPoint ≠ (1 : Circle) := by
  intro h
  have hh := congrArg (fun c : Circle => (c : ℂ)) h
  simp only [windingPhaseCutPoint_coe, Circle.coe_one] at hh
  norm_num at hh

private theorem not_mem_grid_of_first_exp_one (p : ℝ × ℝ)
    (hp : Circle.exp p.1 = 1) : p ∉ windingPhaseGrid := by
  rintro ⟨n, hn⟩
  have h := congrArg (fun q => (argumentPlanePhaseMap q).1) hn
  change (argumentPlanePhaseMap (windingPhaseGridPoint n)).1 =
    (argumentPlanePhaseMap p).1 at h
  rw [argumentPlanePhaseMap_gridPoint] at h
  change windingPhaseCutPoint = Circle.exp p.1 at h
  exact windingPhaseCutPoint_ne_one (h.trans hp)

private theorem not_mem_grid_of_second_exp_one (p : ℝ × ℝ)
    (hp : Circle.exp p.2 = 1) : p ∉ windingPhaseGrid := by
  rintro ⟨n, hn⟩
  have h := congrArg (fun q => (argumentPlanePhaseMap q).2) hn
  change (argumentPlanePhaseMap (windingPhaseGridPoint n)).2 =
    (argumentPlanePhaseMap p).2 at h
  rw [argumentPlanePhaseMap_gridPoint] at h
  change windingPhaseCutPoint = Circle.exp p.2 at h
  exact windingPhaseCutPoint_ne_one (h.trans hp)

/-- Actual deck endpoints are outside the grid, since their phases are one. -/
theorem windingPhaseDeckPoint_not_mem_grid (n : ℤ × ℤ) :
    windingPhaseDeckPoint n ∉ windingPhaseGrid :=
  not_mem_grid_of_first_exp_one _ (Circle.exp_int_mul_two_pi n.1)

/-- The actual common origin of the closing paths. -/
def phaseGridOrigin : PhaseGridComplement :=
  ⟨0, not_mem_grid_of_first_exp_one 0 Circle.exp_zero⟩

/-- The actual endpoint of the deck path. -/
def phaseGridDeckEndpoint (n : ℤ × ℤ) : PhaseGridComplement :=
  ⟨windingPhaseDeckPoint n, windingPhaseDeckPoint_not_mem_grid n⟩

/-- Actual deck translation as a continuous map of the actual complement. -/
def phaseGridDeckTranslation (n : ℤ × ℤ) : C(PhaseGridComplement, PhaseGridComplement) where
  toFun p := ⟨p.val + windingPhaseDeckPoint n,
    fun hp => p.property ((add_windingPhaseDeckPoint_mem_grid_iff p.val n).mp hp)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.add continuous_const

@[simp] theorem phaseGridDeckTranslation_coe (n : ℤ × ℤ) (p : PhaseGridComplement) :
    (phaseGridDeckTranslation n p).val = p.val + windingPhaseDeckPoint n := rfl

private theorem principalInterval_scaled_bounds (a : ℝ)
    (ha0 : -Real.pi < a) (ha1 : a ≤ Real.pi) (t : I) :
    -Real.pi < (t : ℝ) * a ∧ (t : ℝ) * a ≤ Real.pi := by
  constructor
  · by_cases ha : 0 ≤ a
    · have h := mul_nonneg t.property.1 ha
      linarith [Real.pi_pos]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      have h : a ≤ (t : ℝ) * a := by
        simpa only [one_mul] using mul_le_mul_of_nonpos_right t.property.2 ha'
      exact ha0.trans_le h
  · by_cases ha : 0 ≤ a
    · have h : (t : ℝ) * a ≤ a := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 ha
      exact h.trans ha1
    · have h := mul_nonpos_of_nonneg_of_nonpos t.property.1 (le_of_not_ge ha)
      exact h.trans (le_of_lt Real.pi_pos)

private theorem principalInterval_eq_pi_of_scaled_eq (a : ℝ)
    (ha : a ≤ Real.pi) (t : I) (he : (t : ℝ) * a = Real.pi) : a = Real.pi := by
  have ha0 : 0 ≤ a := by
    by_contra h
    have hm := mul_nonpos_of_nonneg_of_nonpos t.property.1 (le_of_not_ge h)
    rw [he] at hm
    exact (not_le_of_gt Real.pi_pos) hm
  have hm : (t : ℝ) * a ≤ a := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 ha0
  rw [he] at hm
  exact le_antisymm ha hm

/-- The genuine radial segment from zero to a principal-square point
outside the grid avoids every grid point. No path avoidance is an input. -/
theorem principalRectangle_radial_not_mem_grid (p : ℝ × ℝ)
    (hlo1 : -Real.pi < p.1) (hhi1 : p.1 ≤ Real.pi)
    (hlo2 : -Real.pi < p.2) (hhi2 : p.2 ≤ Real.pi)
    (hp : p ∉ windingPhaseGrid) (t : I) :
    ((t : ℝ) * p.1, (t : ℝ) * p.2) ∉ windingPhaseGrid := by
  rintro ⟨n, hn⟩
  have hphase := congrArg argumentPlanePhaseMap hn
  rw [argumentPlanePhaseMap_gridPoint] at hphase
  have h1 := congrArg (fun q : Circle × Circle => Complex.arg (q.1 : ℂ)) hphase
  have h2 := congrArg (fun q : Circle × Circle => Complex.arg (q.2 : ℂ)) hphase
  change Complex.arg (windingPhaseCutPoint : ℂ) =
    Complex.arg (Circle.exp ((t : ℝ) * p.1) : ℂ) at h1
  change Complex.arg (windingPhaseCutPoint : ℂ) =
    Complex.arg (Circle.exp ((t : ℝ) * p.2) : ℂ) at h2
  have hb1 := principalInterval_scaled_bounds p.1 hlo1 hhi1 t
  have hb2 := principalInterval_scaled_bounds p.2 hlo2 hhi2 t
  rw [windingPhaseCutPoint_arg, Circle.arg_exp hb1.1 hb1.2] at h1
  rw [windingPhaseCutPoint_arg, Circle.arg_exp hb2.1 hb2.2] at h2
  have he1 := principalInterval_eq_pi_of_scaled_eq p.1 hhi1 t h1.symm
  have he2 := principalInterval_eq_pi_of_scaled_eq p.2 hhi2 t h2.symm
  apply hp
  refine ⟨0, ?_⟩
  ext <;> simp [windingPhaseGridPoint, he1, he2]

/-- The actual selected principal-argument point in the actual complement. -/
def phaseGridPrincipalPoint (z : TwicePuncturedComplex) : PhaseGridComplement :=
  ⟨twicePuncturedPrincipalArgumentPair z,
    twicePuncturedPrincipalArgumentPair_not_mem_grid z⟩

/-- The actual radial principal path, with grid avoidance derived above. -/
def phaseGridPrincipalPath (z : TwicePuncturedComplex) :
    Path phaseGridOrigin (phaseGridPrincipalPoint z) where
  toFun t := ⟨((t : ℝ) * (twicePuncturedPrincipalArgumentPair z).1,
    (t : ℝ) * (twicePuncturedPrincipalArgumentPair z).2), by
      have hb := twicePuncturedPrincipalArgumentPair_bounds z
      exact principalRectangle_radial_not_mem_grid _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
        (twicePuncturedPrincipalArgumentPair_not_mem_grid z) t⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; ext <;> simp [phaseGridOrigin]
  target' := by apply Subtype.ext; ext <;> simp [phaseGridPrincipalPoint]

/-- The actual vertical endpoint, before the horizontal deck segment. -/
def phaseGridVerticalEndpoint (n : ℤ × ℤ) : PhaseGridComplement :=
  ⟨(0, (n.2 : ℝ) * (2 * Real.pi)), not_mem_grid_of_first_exp_one _ Circle.exp_zero⟩

/-- First traverse the actual vertical segment. Its first phase is one. -/
def phaseGridDeckVerticalPath (n : ℤ × ℤ) :
    Path phaseGridOrigin (phaseGridVerticalEndpoint n) where
  toFun t := ⟨(0, (t : ℝ) * ((n.2 : ℝ) * (2 * Real.pi))),
    not_mem_grid_of_first_exp_one _ Circle.exp_zero⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; ext <;> simp [phaseGridOrigin]
  target' := by apply Subtype.ext; ext <;> simp [phaseGridVerticalEndpoint]

/-- Then traverse the actual horizontal segment. Its second phase is one. -/
def phaseGridDeckHorizontalPath (n : ℤ × ℤ) :
    Path (phaseGridVerticalEndpoint n) (phaseGridDeckEndpoint n) where
  toFun t := ⟨((t : ℝ) * ((n.1 : ℝ) * (2 * Real.pi)),
    (n.2 : ℝ) * (2 * Real.pi)),
    not_mem_grid_of_second_exp_one _ (Circle.exp_int_mul_two_pi n.2)⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; ext <;> simp [phaseGridVerticalEndpoint]
  target' := by apply Subtype.ext; ext <;> simp [phaseGridDeckEndpoint, windingPhaseDeckPoint]

/-- The actual selected deck path is FIRST VERTICAL, THEN HORIZONTAL.
This convention makes the later discrepancy rectangle have sign n₁m₂. -/
def phaseGridDeckPath (n : ℤ × ℤ) : Path phaseGridOrigin (phaseGridDeckEndpoint n) :=
  (phaseGridDeckVerticalPath n).trans (phaseGridDeckHorizontalPath n)

/-- The actual two integer increments of the original phase path. -/
def twicePuncturedArgumentDeckIncrement (γ : C(I, TwicePuncturedComplex)) : ℤ × ℤ :=
  (circlePathIntegerIncrement (twicePuncturedComplexZeroPhase.comp γ),
    circlePathIntegerIncrement (twicePuncturedComplexOnePhase.comp γ))

theorem twicePuncturedPathArgumentPair_zero (γ : C(I, TwicePuncturedComplex)) :
    twicePuncturedPathArgumentPair γ 0 = twicePuncturedPrincipalArgumentPair (γ 0) := by
  apply Prod.ext
  · exact circlePathArgumentLift_zero (twicePuncturedComplexZeroPhase.comp γ)
  · exact circlePathArgumentLift_zero (twicePuncturedComplexOnePhase.comp γ)

theorem twicePuncturedPathArgumentPair_one (γ : C(I, TwicePuncturedComplex)) :
    twicePuncturedPathArgumentPair γ 1 = twicePuncturedPrincipalArgumentPair (γ 1) +
      windingPhaseDeckPoint (twicePuncturedArgumentDeckIncrement γ) := by
  apply Prod.ext
  · exact circlePathIntegerIncrement_formula (twicePuncturedComplexZeroPhase.comp γ)
  · exact circlePathIntegerIncrement_formula (twicePuncturedComplexOnePhase.comp γ)

/-- The actual lifted original path as a native path in the grid complement. -/
def phaseGridLiftedOriginalPath (γ : C(I, TwicePuncturedComplex)) :
    Path (phaseGridPrincipalPoint (γ 0))
      (phaseGridDeckTranslation (twicePuncturedArgumentDeckIncrement γ)
        (phaseGridPrincipalPoint (γ 1))) where
  toFun t := ⟨twicePuncturedPathArgumentPair γ t,
    twicePuncturedPathArgumentPair_not_mem_grid γ t⟩
  continuous_toFun := Continuous.subtype_mk (twicePuncturedPathArgumentPair γ).continuous _
  source' := Subtype.ext (twicePuncturedPathArgumentPair_zero γ)
  target' := Subtype.ext (twicePuncturedPathArgumentPair_one γ)

/-- The actual translated terminal principal path, starting at the
same deck endpoint used by the actual closing loop. -/
def phaseGridTranslatedPrincipalPath (n : ℤ × ℤ) (z : TwicePuncturedComplex) :
    Path (phaseGridDeckEndpoint n) (phaseGridDeckTranslation n (phaseGridPrincipalPoint z)) :=
  ((phaseGridPrincipalPath z).map (phaseGridDeckTranslation n).continuous).cast
    (by apply Subtype.ext; simp [phaseGridOrigin, phaseGridDeckEndpoint]) rfl

/-- The genuine closed argument-plane loop associated with an original
path. Its four pieces have proved actual matching endpoints. -/
def twicePuncturedPhaseClosingLoop (γ : C(I, TwicePuncturedComplex)) :
    Path phaseGridOrigin phaseGridOrigin :=
  (((phaseGridPrincipalPath (γ 0)).trans (phaseGridLiftedOriginalPath γ)).trans
    (phaseGridTranslatedPrincipalPath (twicePuncturedArgumentDeckIncrement γ) (γ 1)).symm).trans
    (phaseGridDeckPath (twicePuncturedArgumentDeckIncrement γ)).symm

/-- Its actual coordinate path, with both endpoints at the same origin. -/
def twicePuncturedPhaseClosingCoordinatePath (γ : C(I, TwicePuncturedComplex)) :
    C(I, ℝ × ℝ) :=
  ⟨fun t => (twicePuncturedPhaseClosingLoop γ t).val,
    continuous_subtype_val.comp (twicePuncturedPhaseClosingLoop γ).continuous⟩

theorem twicePuncturedPhaseClosingCoordinatePath_closed (γ : C(I, TwicePuncturedComplex)) :
    twicePuncturedPhaseClosingCoordinatePath γ 0 =
      twicePuncturedPhaseClosingCoordinatePath γ 1 := by
  change (twicePuncturedPhaseClosingLoop γ 0).val = (twicePuncturedPhaseClosingLoop γ 1).val
  rw [Path.source, Path.target]

theorem twicePuncturedPhaseClosingCoordinatePath_not_mem_grid
    (γ : C(I, TwicePuncturedComplex)) (t : I) :
    twicePuncturedPhaseClosingCoordinatePath γ t ∉ windingPhaseGrid :=
  (twicePuncturedPhaseClosingLoop γ t).property

/-- The actual integer winding total of the actual closing loop. This is
an actual function of the original path; its coboundary formula remains
to be proved from actual concatenation and rectangle computations. -/
def twicePuncturedPathClosingWinding (γ : C(I, TwicePuncturedComplex)) : ℤ :=
  phaseGridPathTotalWinding (twicePuncturedPhaseClosingCoordinatePath γ)
    (twicePuncturedPhaseClosingCoordinatePath_closed γ)
    (twicePuncturedPhaseClosingCoordinatePath_not_mem_grid γ)

end ChenRanks
