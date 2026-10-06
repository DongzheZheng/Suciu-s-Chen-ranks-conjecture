import Mathlib

/-!
# A finite set of actual valuation rows detects the entire valuation system

The row index type may be infinite or empty.  Finite-dimensional linear algebra
selects a finite set of indices from that very system whose rational rows span
every row.  Consequently those indices detect the full complex coefficient
kernel and the full integer product kernel, simultaneously for all vectors.

No finite sampling hypothesis or preselected detector is assumed.  The rows
are integer vectors; their interpretation as actual relative valuations will
be supplied by the field-theoretic part of the project.
-/

open scoped BigOperators

namespace ChenRanks

noncomputable section

variable {D n : Type*} [Fintype n]

/-- An integer valuation row, viewed as a rational vector. -/
def rationalValuationRow (r : D → n → ℤ) (d : D) : n → ℚ :=
  fun j ↦ (r d j : ℚ)

/-- The complex scalar residue associated to a coefficient vector. -/
def complexRowDot (r : D → n → ℤ) (β : n → ℂ) (d : D) : ℂ :=
  ∑ j, (r d j : ℂ) * β j

/-- The valuation of the integer product attached to an exponent vector. -/
def integerRowDot (r : D → n → ℤ) (a : n → ℤ) (d : D) : ℤ :=
  ∑ j, r d j * a j

/-- A rational-linear functional with values in an arbitrary rational module. -/
def rationalRowFunctional {A : Type*} [AddCommGroup A] [Module ℚ A]
    (β : n → A) : (n → ℚ) →ₗ[ℚ] A where
  toFun x := ∑ j, x j • β j
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp]
theorem rationalRowFunctional_complex_apply
    (r : D → n → ℤ) (β : n → ℂ) (d : D) :
    rationalRowFunctional β (rationalValuationRow r d) = complexRowDot r β d := by
  change (∑ j, (rationalValuationRow r d) j • β j) =
    ∑ j, (r d j : ℂ) * β j
  simp only [rationalValuationRow, Rat.smul_def, Rat.cast_intCast]

@[simp]
theorem complexRowDot_intCast (r : D → n → ℤ) (a : n → ℤ) (d : D) :
    complexRowDot r (fun j ↦ (a j : ℂ)) d = (integerRowDot r a d : ℂ) := by
  simp only [complexRowDot, integerRowDot, Int.cast_sum, Int.cast_mul]

/-- Select a finite subset of the actual row indices whose rational span is the
span of the complete, possibly infinite, row system. -/
theorem exists_finset_rational_rows_span (r : D → n → ℤ) :
    ∃ S : Finset D,
      Submodule.span ℚ (rationalValuationRow r '' (S : Set D)) =
        Submodule.span ℚ (Set.range (rationalValuationRow r)) := by
  classical
  obtain ⟨t, htSub, _htCard, htSpan, _htIndependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℚ
      (Set.range (rationalValuationRow r))
  let pick : ↥t → D := fun x ↦ Classical.choose (htSub x.property)
  have hPick (x : ↥t) : rationalValuationRow r (pick x) = (x : n → ℚ) :=
    Classical.choose_spec (htSub x.property)
  let S : Finset D := Finset.univ.image pick
  refine ⟨S, le_antisymm ?_ ?_⟩
  · apply Submodule.span_mono
    rintro x ⟨d, _hd, rfl⟩
    exact Set.mem_range_self d
  · rw [← htSpan]
    apply Submodule.span_mono
    intro x hx
    refine ⟨pick ⟨x, hx⟩, ?_, hPick ⟨x, hx⟩⟩
    change pick ⟨x, hx⟩ ∈ Finset.univ.image pick
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

/-- Any rational-linear test that vanishes on the chosen rows vanishes on
every row of the full system. -/
theorem all_rows_zero_of_span_eq
    {A : Type*} [AddCommGroup A] [Module ℚ A]
    (r : D → n → ℤ) (S : Finset D)
    (hSpan : Submodule.span ℚ (rationalValuationRow r '' (S : Set D)) =
      Submodule.span ℚ (Set.range (rationalValuationRow r)))
    (β : n → A)
    (h : ∀ d ∈ S, rationalRowFunctional β (rationalValuationRow r d) = 0) :
    ∀ d, rationalRowFunctional β (rationalValuationRow r d) = 0 := by
  have hKer : Submodule.span ℚ (rationalValuationRow r '' (S : Set D)) ≤
      LinearMap.ker (rationalRowFunctional β) := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, hd, rfl⟩
    exact h d hd
  intro d
  apply hKer
  rw [hSpan]
  exact Submodule.subset_span (Set.mem_range_self d)

/-- Rational row spanning suffices even when the coefficient vector is complex. -/
theorem complex_kernel_iff_of_span_eq
    (r : D → n → ℤ) (S : Finset D)
    (hSpan : Submodule.span ℚ (rationalValuationRow r '' (S : Set D)) =
      Submodule.span ℚ (Set.range (rationalValuationRow r)))
    (β : n → ℂ) :
    (∀ d ∈ S, complexRowDot r β d = 0) ↔ ∀ d, complexRowDot r β d = 0 := by
  constructor
  · intro h
    have h' : ∀ d ∈ S, rationalRowFunctional β (rationalValuationRow r d) = 0 := by
      simpa only [rationalRowFunctional_complex_apply] using h
    simpa only [rationalRowFunctional_complex_apply] using
      all_rows_zero_of_span_eq r S hSpan β h'
  · intro h d _hd
    exact h d

/-- In particular, every integer product invisible to the selected rows is
invisible to all relative valuation rows, not just the sample. -/
theorem integer_kernel_iff_of_span_eq
    (r : D → n → ℤ) (S : Finset D)
    (hSpan : Submodule.span ℚ (rationalValuationRow r '' (S : Set D)) =
      Submodule.span ℚ (Set.range (rationalValuationRow r)))
    (a : n → ℤ) :
    (∀ d ∈ S, integerRowDot r a d = 0) ↔ ∀ d, integerRowDot r a d = 0 := by
  constructor
  · intro h
    have hC : ∀ d ∈ S, complexRowDot r (fun j ↦ (a j : ℂ)) d = 0 := by
      simpa only [complexRowDot_intCast, Int.cast_eq_zero] using h
    have hAll := (complex_kernel_iff_of_span_eq r S hSpan (fun j ↦ (a j : ℂ))).mp hC
    simpa only [complexRowDot_intCast, Int.cast_eq_zero] using hAll
  · intro h d _hd
    exact h d

/-- One finite subset of actual rows controls all complex coefficient vectors
and all integer exponent vectors simultaneously. -/
theorem exists_finite_rows_with_full_kernel_control (r : D → n → ℤ) :
    ∃ S : Finset D,
      Submodule.span ℚ (rationalValuationRow r '' (S : Set D)) =
        Submodule.span ℚ (Set.range (rationalValuationRow r)) ∧
      (∀ β : n → ℂ,
        (∀ d ∈ S, complexRowDot r β d = 0) ↔ ∀ d, complexRowDot r β d = 0) ∧
      (∀ a : n → ℤ,
        (∀ d ∈ S, integerRowDot r a d = 0) ↔ ∀ d, integerRowDot r a d = 0) := by
  obtain ⟨S, hSpan⟩ := exists_finset_rational_rows_span r
  exact ⟨S, hSpan, complex_kernel_iff_of_span_eq r S hSpan,
    integer_kernel_iff_of_span_eq r S hSpan⟩

end

end ChenRanks
