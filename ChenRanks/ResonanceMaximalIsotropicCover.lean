import ChenRanks.MaximalIsotropicExtension

/-!
# The actual resonance point set is covered by maximal isotropic spaces

The actual witness `a ∧ b ∈ I`, with `b` outside the line through a nonzero
`a`, produces the actual isotropic plane spanned by `a` and `b`. The
Noetherian extension theorem then produces a maximal isotropic subspace
containing that plane. The resulting cover may have infinitely many members;
no component finiteness or scheme reducedness is asserted here.
-/

namespace ChenRanks.Resonance

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

private theorem exteriorWedge_swap (a b : E) :
    exteriorWedge (k := k) a b = -exteriorWedge (k := k) b a := by
  apply (ExteriorAlgebra.exteriorPower k 2 E).subtype_injective
  change (exteriorWedge (k := k) a b : ExteriorAlgebra k E) =
    -(exteriorWedge (k := k) b a : ExteriorAlgebra k E)
  rw [exteriorWedge_coe, exteriorWedge_coe]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

/-- The actual span of a quadratic exterior relation is cup-isotropic.
Alternation and bilinearity are used inside the actual exterior algebra. -/
theorem span_pair_isCupIsotropic
    (I : Submodule k (⋀[k]^2 E)) (a b : E)
    (hab : exteriorWedge (k := k) a b ∈ I) :
    IsCupIsotropic I (Submodule.span k ({a, b} : Set E)) := by
  have hba : exteriorWedge (k := k) b a ∈ I := by
    rw [exteriorWedge_swap b a]
    exact I.neg_mem hab
  have hgen : ∀ x ∈ ({a, b} : Set E), ∀ y ∈ ({a, b} : Set E),
      exteriorWedge (k := k) x y ∈ I := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simpa only [exteriorWedge_self] using I.zero_mem
    · exact hab
    · exact hba
    · simpa only [exteriorWedge_self] using I.zero_mem
  apply (isCupIsotropic_iff I _).mpr
  intro x hx y hy
  exact LinearMap.BilinMap.apply_apply_mem_of_mem_span I
    ({a, b} : Set E) ({a, b} : Set E)
    (exteriorWedgeBilin (k := k)) hgen x y hx hy

section FiniteDimension

variable [FiniteDimensional k E]

/-- The genuine resonance witness generates a subspace of dimension at
least two. This is derived from being outside the actual one-dimensional
span, rather than supplied as a plane assumption. -/
theorem two_le_finrank_span_pair_of_not_mem_line
    (a b : E) (ha : a ≠ 0) (hba : b ∉ k ∙ a) :
    2 ≤ Module.finrank k (Submodule.span k ({a, b} : Set E)) := by
  let U := Submodule.span k ({a, b} : Set E)
  have haU : a ∈ U := Submodule.subset_span (by simp)
  have hbU : b ∈ U := Submodule.subset_span (by simp)
  have hle : k ∙ a ≤ U :=
    (Submodule.span_singleton_le_iff_mem a U).mpr haU
  have hlt : k ∙ a < U :=
    SetLike.lt_iff_le_and_exists.mpr ⟨hle, b, hbU, hba⟩
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_span_singleton ha] at hdim
  change 2 ≤ Module.finrank k U
  omega

/-- The actual span of a genuine nonzero resonance witness has dimension
exactly two, providing the literal plane needed for a Grassmannian chart. -/
theorem finrank_span_pair_eq_two_of_not_mem_line
    (a b : E) (ha : a ≠ 0) (hba : b ∉ k ∙ a) :
    Module.finrank k (Submodule.span k ({a, b} : Set E)) = 2 := by
  classical
  have habne : a ≠ b := by
    intro hab
    apply hba
    rw [← hab]
    exact Submodule.mem_span_singleton_self a
  have hupper : Module.finrank k (Submodule.span k ({a, b} : Set E)) ≤ 2 := by
    have hset : (({a, b} : Finset E) : Set E) = ({a, b} : Set E) := by
      ext x
      simp
    have hupperSet := finrank_span_finset_le_card (R := k) ({a, b} : Finset E)
    change Module.finrank k
      (Submodule.span k (({a, b} : Finset E) : Set E)) ≤
        ({a, b} : Finset E).card at hupperSet
    rw [hset] at hupperSet
    simpa [habne] using hupperSet
  exact le_antisymm hupper
    (two_le_finrank_span_pair_of_not_mem_line a b ha hba)

/-- Every nonzero point of the actual resonance set lies in an actual
maximal isotropic subspace of dimension at least two. -/
theorem nonzero_resonance_mem_maximal_isotropic
    (I : Submodule k (⋀[k]^2 E)) {a : E}
    (ha : a ≠ 0) (haR : a ∈ resonance I) :
    ∃ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
      2 ≤ Module.finrank k P ∧ a ∈ P := by
  obtain ⟨b, hba, hab⟩ := (mem_resonance_iff I ha).mp haR
  let U := Submodule.span k ({a, b} : Set E)
  have hU : IsIsotropic (relationWedge (cupQuotient I)) U :=
    (isCupIsotropic_iff_isIsotropic I U).mp
      (span_pair_isCupIsotropic I a b hab)
  have hdim : 2 ≤ Module.finrank k U :=
    two_le_finrank_span_pair_of_not_mem_line a b ha hba
  obtain ⟨P, hUP, hP, hdimP⟩ :=
    exists_maximal_isotropic_extension_finrank_ge
      (relationWedge (cupQuotient I)) U hU 2 hdim
  exact ⟨P, hP, hdimP, hUP (Submodule.subset_span (by simp))⟩

/-- Pointwise description by actual maximal isotropic subspaces. The
origin remains included even when no dimension-two isotropic space exists. -/
theorem mem_resonance_iff_zero_or_mem_maximal_isotropic
    (I : Submodule k (⋀[k]^2 E)) (a : E) :
    a ∈ resonance I ↔ a = 0 ∨ ∃ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
      2 ≤ Module.finrank k P ∧ a ∈ P := by
  constructor
  · intro haR
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (nonzero_resonance_mem_maximal_isotropic I ha haR)
  · rintro (rfl | ⟨P, hP, hdimP, haP⟩)
    · exact zero_mem_resonance I
    · exact isotropic_subspace_subset_resonance I P hdimP
        ((isCupIsotropic_iff_isIsotropic I P).mpr hP.1) haP

/-- The actual resonance point set is the origin together with the union
of all actual maximal isotropic subspaces of dimension at least two.
The indexing family is deliberately not assumed or proved finite. -/
theorem resonance_eq_zero_union_maximal_isotropic
    (I : Submodule k (⋀[k]^2 E)) :
    resonance I = {0} ∪
      ⋃ P ∈ {P : Submodule k E |
        IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
          2 ≤ Module.finrank k P}, (P : Set E) := by
  ext a
  rw [mem_resonance_iff_zero_or_mem_maximal_isotropic]
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion,
    Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro (ha | ⟨P, hP, hdimP, haP⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨P, ⟨hP, hdimP⟩, haP⟩
  · rintro (ha | ⟨P, ⟨hP, hdimP⟩, haP⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨P, hP, hdimP, haP⟩

end FiniteDimension

end ChenRanks.Resonance
