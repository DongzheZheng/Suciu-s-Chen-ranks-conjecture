import ChenRanks.SeparatedMaximalIsotropicFinite

/-!
# Actual finite maximal-isotropic types and their dimension counts

The subtype consists of the original maximal isotropic subspaces for the
actual exterior map, of dimension at least two. Its Fintype is constructed
from the proved finite-family theorem. The dimension count is the genuine
cardinality of its corresponding actual dimension fiber; no counts, target
Chen formula, or irreducible-component classification are input.

These are counts of actual maximal isotropic subspaces. Identifying them
with projective resonance-scheme irreducible-component counts, or with the
topological h_m in the Chen theorem, remains a separate comparison theorem.
No comparison with the topological cup or irreducible components is asserted.
-/

noncomputable section

namespace ChenRanks.Resonance

universe u v w

variable {k : Type u} {E : Type v} {W : Type w}
  [Field k] [AddCommGroup E] [Module k E]
  [AddCommGroup W] [Module k W] [FiniteDimensional k E] [Infinite k]

/-- Actual finiteness for the original exterior map, obtained by the proved
kernel-quotient comparison and the actual finite frame-cover theorem. -/
theorem original_maximal_isotropic_finite_of_separated
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) :
    {P : Submodule k E |
      IsMaximalIsotropic (relationWedge φ) P ∧ 2 ≤ Module.finrank k P}.Finite := by
  have hsepI : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient (LinearMap.ker φ))) P →
      2 ≤ Module.finrank k P →
      mixedExterior P ⊓ LinearMap.ker φ = pureExterior P :=
    fun P hP hdim ↦ hsep P ((isMaximalIsotropic_kernel_quotient_iff φ P).mp hP) hdim
  have hfinite := finite_maximal_cup_isotropic_of_separated (LinearMap.ker φ) hsepI
  simpa only [isMaximalIsotropic_kernel_quotient_iff] using hfinite

/-- The genuine original maximal-isotropic family, restricted to the
dimensions relevant for the actual resonance cover. -/
abbrev OriginalMaximalIsotropicFamily (φ : (⋀[k]^2 E) →ₗ[k] W) :=
  {P : Submodule k E //
    IsMaximalIsotropic (relationWedge φ) P ∧ 2 ≤ Module.finrank k P}

/-- Its actual finite enumeration comes from the proved actual finite set,
rather than from an assumed component list or assumed finite cardinality. -/
@[implicit_reducible]
def originalMaximalIsotropicFamilyFintype
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) :
    Fintype (OriginalMaximalIsotropicFamily φ) :=
  (original_maximal_isotropic_finite_of_separated φ hsep).fintype

/-- The genuine cardinality of the actual dimension-m fiber of the proved
finite original maximal-isotropic family. -/
def originalMaximalIsotropicDimensionCount
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) (m : ℕ) : ℕ := by
  classical
  letI := originalMaximalIsotropicFamilyFintype φ hsep
  exact Fintype.card {P : OriginalMaximalIsotropicFamily φ // Module.finrank k P.val = m}

/-- The count is nonzero exactly when the actual original maximal
isotropic space of that dimension exists. -/
theorem originalMaximalIsotropicDimensionCount_pos_iff
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) (m : ℕ) :
    0 < originalMaximalIsotropicDimensionCount φ hsep m ↔
      ∃ P : Submodule k E, IsMaximalIsotropic (relationWedge φ) P ∧
        2 ≤ Module.finrank k P ∧ Module.finrank k P = m := by
  classical
  letI := originalMaximalIsotropicFamilyFintype φ hsep
  unfold originalMaximalIsotropicDimensionCount
  rw [Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨P, hdim⟩⟩
    exact ⟨P.val, P.property.1, P.property.2, hdim⟩
  · rintro ⟨P, hP, hdim, hm⟩
    exact ⟨⟨⟨P, hP, hdim⟩, hm⟩⟩

/-- The actual dimension count has no artificial dimension-zero or
dimension-one entries: such fibers of the actual subtype are empty. -/
theorem originalMaximalIsotropicDimensionCount_eq_zero_of_lt_two
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) (m : ℕ) (hm : m < 2) :
    originalMaximalIsotropicDimensionCount φ hsep m = 0 := by
  by_contra h
  have hpos := (originalMaximalIsotropicDimensionCount_pos_iff φ hsep m).mp
    (Nat.pos_of_ne_zero h)
  obtain ⟨P, _hP, hdim, heq⟩ := hpos
  omega

/-- Actual submodule dimension bounds give finite support of the dimension
count within the true dimension of the original E. -/
theorem originalMaximalIsotropicDimensionCount_eq_zero_of_finrank_lt
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) (m : ℕ)
    (hm : Module.finrank k E < m) :
    originalMaximalIsotropicDimensionCount φ hsep m = 0 := by
  by_contra h
  obtain ⟨P, _hP, _hdim, heq⟩ :=
    (originalMaximalIsotropicDimensionCount_pos_iff φ hsep m).mp (Nat.pos_of_ne_zero h)
  have hle := P.finrank_le
  omega

/-- The intrinsic count does not depend on which proof of the actual
separation theorem is used to construct its finite enumeration. -/
theorem originalMaximalIsotropicDimensionCount_proof_irrelevant
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep hsep' : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P) (m : ℕ) :
    originalMaximalIsotropicDimensionCount φ hsep m =
      originalMaximalIsotropicDimensionCount φ hsep' m := rfl

end ChenRanks.Resonance
