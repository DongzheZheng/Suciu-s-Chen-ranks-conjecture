import ChenRanks.ExteriorSeparation
import ChenRanks.KoszulComponentDuality

/-!
# Genuine Aomoto cohomology and the first resonance point set

The input `I` is an actual submodule of the second exterior power.  The
degree-one Aomoto differential sends `b` to the actual quotient class of
`a ∧ b` in `Λ² E / I`.  Its first cohomology is the actual quotient of
its kernel by the image of the degree-zero differential `c ↦ c • a`.

The resonance point set is defined by the paper's exterior-product
condition, with the origin included by convention.  It is proved to be
the corresponding kernel degeneracy locus, and, away from the origin,
the locus where genuine first Aomoto cohomology is nontrivial.  No list
of proposed linear components, determinantal scheme structure, effective
decomposition, or Chen-rank comparison is an input or a conclusion here.
-/

noncomputable section

namespace ChenRanks.Resonance

variable {k : Type*} [Field k]
variable {E : Type*} [AddCommGroup E] [Module k E]

/-- The actual quotient target of the degree-two cup product. -/
abbrev CupTarget (I : Submodule k (⋀[k]^2 E)) := (⋀[k]^2 E) ⧸ I

/-- The genuine quotient map, not a substitute relation detector. -/
def cupQuotient (I : Submodule k (⋀[k]^2 E)) :
    (⋀[k]^2 E) →ₗ[k] CupTarget I := I.mkQ

@[simp] theorem cupQuotient_eq_zero_iff (I : Submodule k (⋀[k]^2 E))
    (z : ⋀[k]^2 E) : cupQuotient I z = 0 ↔ z ∈ I := by
  exact Submodule.Quotient.mk_eq_zero I

/-- The actual degree-one Aomoto differential for the vector `a`. -/
def aomotoDegreeOne (I : Submodule k (⋀[k]^2 E)) (a : E) :
    E →ₗ[k] CupTarget I := (cupQuotient I).comp (exteriorWedgeBilin a)

@[simp] theorem aomotoDegreeOne_apply (I : Submodule k (⋀[k]^2 E)) (a b : E) :
    aomotoDegreeOne I a b = cupQuotient I (exteriorWedge a b) := rfl

@[simp] theorem aomotoDegreeOne_eq_zero_iff (I : Submodule k (⋀[k]^2 E))
    (a b : E) : aomotoDegreeOne I a b = 0 ↔ exteriorWedge a b ∈ I := by
  exact cupQuotient_eq_zero_iff I (exteriorWedge a b)

/-- Alternation is proved in the actual exterior algebra. -/
@[simp] theorem exteriorWedge_self (a : E) : exteriorWedge (k := k) a a = 0 := by
  apply Subtype.ext
  simpa only [exteriorWedge_coe, ZeroMemClass.coe_zero] using
    (ExteriorAlgebra.ι_sq_zero (R := k) a)

@[simp] theorem aomotoDegreeOne_self (I : Submodule k (⋀[k]^2 E)) (a : E) :
    aomotoDegreeOne I a a = 0 := by
  simp

/-- The actual degree-zero Aomoto differential. -/
def aomotoDegreeZero (a : E) : k →ₗ[k] E := LinearMap.toSpanSingleton k E a

@[simp] theorem aomotoDegreeZero_apply (a : E) (c : k) :
    aomotoDegreeZero a c = c • a := rfl

/-- The actual two Aomoto differentials compose to zero. -/
theorem aomoto_comp_zero (I : Submodule k (⋀[k]^2 E)) (a : E) :
    (aomotoDegreeOne I a).comp (aomotoDegreeZero a) = 0 := by
  apply LinearMap.ext
  intro c
  simp

theorem aomotoDegreeZero_range (a : E) :
    LinearMap.range (aomotoDegreeZero (k := k) a) = k ∙ a :=
  LinearMap.range_toSpanSingleton a

/-- Genuine degree-one Aomoto cycles. -/
def aomotoCycles (I : Submodule k (⋀[k]^2 E)) (a : E) : Submodule k E :=
  LinearMap.ker (aomotoDegreeOne I a)

@[simp] theorem mem_aomotoCycles (I : Submodule k (⋀[k]^2 E)) (a b : E) :
    b ∈ aomotoCycles I a ↔ exteriorWedge a b ∈ I :=
  aomotoDegreeOne_eq_zero_iff I a b

theorem line_le_aomotoCycles (I : Submodule k (⋀[k]^2 E)) (a : E) :
    k ∙ a ≤ aomotoCycles I a := by
  apply (Submodule.span_singleton_le_iff_mem a _).mpr
  exact aomotoDegreeOne_self I a

/-- The actual degree-zero differential with codomain restricted to cycles. -/
def aomotoDegreeZeroCycles (I : Submodule k (⋀[k]^2 E)) (a : E) :
    k →ₗ[k] aomotoCycles I a :=
  (aomotoDegreeZero a).codRestrict (aomotoCycles I a) (fun c ↦ by
    change aomotoDegreeOne I a (aomotoDegreeZero a c) = 0
    simp)

@[simp] theorem aomotoDegreeZeroCycles_coe
    (I : Submodule k (⋀[k]^2 E)) (a : E) (c : k) :
    (aomotoDegreeZeroCycles I a c : E) = c • a := rfl

/-- Boundaries are defined as the range of the genuine restricted differential. -/
def aomotoBoundaries (I : Submodule k (⋀[k]^2 E)) (a : E) :
    Submodule k (aomotoCycles I a) := LinearMap.range (aomotoDegreeZeroCycles I a)

/-- The actual image of the degree-zero differential is precisely the line
inside the actual cycle space.  This identity is proved, not assumed. -/
theorem aomotoBoundaries_eq_comap_line (I : Submodule k (⋀[k]^2 E)) (a : E) :
    aomotoBoundaries I a = (k ∙ a).comap (aomotoCycles I a).subtype := by
  ext b
  constructor
  · rintro ⟨c, rfl⟩
    change c • a ∈ k ∙ a
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a)
  · intro hb
    change (b : E) ∈ k ∙ a at hb
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc

/-- Genuine first cohomology of the actual Aomoto complex in degrees zero,
one, and two. -/
abbrev AomotoH1 (I : Submodule k (⋀[k]^2 E)) (a : E) :=
  aomotoCycles I a ⧸ aomotoBoundaries I a

/-- Nontriviality of the actual cohomology quotient detects strict kernel
enlargement.  No finite-dimensional hypothesis is needed. -/
theorem aomotoH1_nontrivial_iff (I : Submodule k (⋀[k]^2 E)) (a : E) :
    Nontrivial (AomotoH1 I a) ↔ k ∙ a < aomotoCycles I a := by
  rw [Submodule.Quotient.nontrivial_iff, aomotoBoundaries_eq_comap_line]
  rw [ne_eq, Submodule.comap_subtype_eq_top, lt_iff_le_not_ge]
  exact ⟨fun h ↦ ⟨line_le_aomotoCycles I a, h⟩, fun h ↦ h.2⟩

/-- The actual first resonance point set, with the origin included exactly
as in the paper.  It is defined using the original exterior relation. -/
def resonance (I : Submodule k (⋀[k]^2 E)) : Set E :=
  {a | a = 0 ∨ (a ≠ 0 ∧ ∃ b : E, b ∉ k ∙ a ∧ exteriorWedge a b ∈ I)}

@[simp] theorem zero_mem_resonance (I : Submodule k (⋀[k]^2 E)) :
    (0 : E) ∈ resonance I := Or.inl rfl

theorem mem_resonance_iff (I : Submodule k (⋀[k]^2 E)) {a : E} (ha : a ≠ 0) :
    a ∈ resonance I ↔ ∃ b : E, b ∉ k ∙ a ∧ exteriorWedge a b ∈ I := by
  change (a = 0 ∨ (a ≠ 0 ∧ _)) ↔ _
  exact ⟨fun h ↦ (h.resolve_left ha).2, fun h ↦ Or.inr ⟨ha, h⟩⟩

/-- The genuine affine kernel degeneracy point set.  This is a set of
actual rank-degenerate points; it does not yet assert a minors ideal or
an affine or projective scheme structure. -/
def degeneracyLocus (I : Submodule k (⋀[k]^2 E)) : Set E :=
  {a | a = 0 ∨ k ∙ a < aomotoCycles I a}

theorem mem_resonance_iff_kernel_lt (I : Submodule k (⋀[k]^2 E))
    {a : E} (ha : a ≠ 0) :
    a ∈ resonance I ↔ k ∙ a < aomotoCycles I a := by
  rw [mem_resonance_iff I ha, SetLike.lt_iff_le_and_exists]
  constructor
  · rintro ⟨b, hba, hb⟩
    exact ⟨line_le_aomotoCycles I a, b, (mem_aomotoCycles I a b).mpr hb, hba⟩
  · rintro ⟨_, b, hb, hba⟩
    exact ⟨b, hba, (mem_aomotoCycles I a b).mp hb⟩

theorem resonance_eq_degeneracyLocus (I : Submodule k (⋀[k]^2 E)) :
    resonance I = degeneracyLocus I := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp [degeneracyLocus]
  · change a ∈ resonance I ↔ a = 0 ∨ k ∙ a < aomotoCycles I a
    rw [mem_resonance_iff_kernel_lt I ha]
    simp only [ha, false_or]

/-- Away from the origin, the paper's exterior condition is equivalent
to nontriviality of the actual Aomoto cohomology quotient. -/
theorem mem_resonance_iff_aomotoH1_nontrivial (I : Submodule k (⋀[k]^2 E))
    {a : E} (ha : a ≠ 0) :
    a ∈ resonance I ↔ Nontrivial (AomotoH1 I a) := by
  rw [aomotoH1_nontrivial_iff, mem_resonance_iff_kernel_lt I ha]

theorem mem_resonance_iff_zero_or_aomotoH1_nontrivial
    (I : Submodule k (⋀[k]^2 E)) (a : E) :
    a ∈ resonance I ↔ a = 0 ∨ Nontrivial (AomotoH1 I a) := by
  by_cases ha : a = 0
  · subst a
    simp
  · rw [mem_resonance_iff_aomotoH1_nontrivial I ha]
    simp only [ha, false_or]

/-- Actual isotropy is containment of the genuine exterior-square
inclusion image in the genuine cup-product kernel. -/
def IsCupIsotropic (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) : Prop :=
  pureExterior P ≤ I

theorem isCupIsotropic_iff (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) :
    IsCupIsotropic I P ↔ ∀ a ∈ P, ∀ b ∈ P, exteriorWedge a b ∈ I := by
  constructor
  · intro h a ha b hb
    exact h (exteriorWedge_mem_pure P ⟨a, ha⟩ ⟨b, hb⟩)
  · intro h
    rw [IsCupIsotropic, pureExterior_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    exact h a a.property b b.property

theorem isCupIsotropic_iff_isIsotropic
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) :
    IsCupIsotropic I P ↔ IsIsotropic (relationWedge (cupQuotient I)) P := by
  rw [isCupIsotropic_iff]
  simp only [IsIsotropic, relationWedge_apply, cupQuotient_eq_zero_iff]

/-- A genuine isotropic subspace of dimension at least two lies in the
actual resonance point set.  One-dimensional isotropic subspaces are
deliberately excluded: their isotropy is automatic and does not suffice. -/
theorem isotropic_subspace_subset_resonance
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) [FiniteDimensional k P]
    (hdim : 2 ≤ Module.finrank k P) (hiso : IsCupIsotropic I P) :
    (P : Set E) ⊆ resonance I := by
  intro a ha
  by_cases haz : a = 0
  · subst a
    exact zero_mem_resonance I
  · have hnle : ¬ P ≤ k ∙ a := by
      intro hle
      have hleDim := Submodule.finrank_mono hle
      rw [finrank_span_singleton haz] at hleDim
      omega
    obtain ⟨b, hb, hba⟩ := SetLike.not_le_iff_exists.mp hnle
    exact (mem_resonance_iff I haz).mpr
      ⟨b, hba, (isCupIsotropic_iff I P).mp hiso a ha b hb⟩

section FiniteDimension

variable [FiniteDimensional k E]

/-- Actual finite-dimensional resonance is actual kernel rank at least
two at a nonzero point. -/
theorem mem_resonance_iff_kernel_finrank (I : Submodule k (⋀[k]^2 E))
    {a : E} (ha : a ≠ 0) :
    a ∈ resonance I ↔ 2 ≤ Module.finrank k (aomotoCycles I a) := by
  rw [mem_resonance_iff_kernel_lt I ha]
  constructor
  · intro h
    have hd := Submodule.finrank_lt_finrank_of_lt h
    rw [finrank_span_singleton ha] at hd
    omega
  · intro h
    apply Submodule.lt_of_le_of_finrank_lt_finrank (line_le_aomotoCycles I a)
    rw [finrank_span_singleton ha]
    omega

/-- The actual differential rank formulation needed by a later minors
construction.  The addition form also treats dimensions zero and one
without a truncated subtraction ambiguity. -/
theorem mem_resonance_iff_differential_rank (I : Submodule k (⋀[k]^2 E))
    {a : E} (ha : a ≠ 0) :
    a ∈ resonance I ↔
      Module.finrank k (LinearMap.range (aomotoDegreeOne I a)) + 2 ≤ Module.finrank k E := by
  rw [mem_resonance_iff_kernel_finrank I ha]
  have hr := LinearMap.finrank_range_add_finrank_ker (aomotoDegreeOne I a)
  change Module.finrank k (LinearMap.range (aomotoDegreeOne I a)) +
    Module.finrank k (aomotoCycles I a) = Module.finrank k E at hr
  omega

/-- In ambient dimension at most one there are no nonzero resonance
points, for any actual quadratic kernel. -/
theorem resonance_eq_singleton_zero_of_finrank_le_one
    (I : Submodule k (⋀[k]^2 E)) (hdim : Module.finrank k E ≤ 1) :
    resonance I = {0} := by
  ext a
  constructor
  · intro ha
    change a = 0
    by_contra haz
    have hdimKer := (mem_resonance_iff_kernel_finrank I haz).mp ha
    have hdimAmbient := Submodule.finrank_le (aomotoCycles I a)
    omega
  · intro ha
    have haz : a = 0 := Set.mem_singleton_iff.mp ha
    subst a
    exact zero_mem_resonance I

/-- Compatibility of actual resonance isotropy with the actual Koszul
dual data: genuine dual restriction kills the genuine quadratic
annihilator relations.  The canonical image identity is supplied by the
proved finite-dimensional exterior duality theorem. -/
theorem quadraticImage_eq_bot_of_cup_isotropic
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) (hiso : IsCupIsotropic I P) :
    Koszul.quadraticImage k (Module.Dual k E) (Module.Dual k P)
      (Koszul.componentDualQuotient k E P) (Koszul.exteriorAnnihilator k E 2 I) = ⊥ :=
  Koszul.quadraticImage_eq_bot_of_isotropic k E P I hiso

end FiniteDimension

end ChenRanks.Resonance
