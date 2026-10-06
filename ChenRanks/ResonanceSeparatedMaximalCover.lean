import ChenRanks.ResonanceMaximalIsotropicCover
import ChenRanks.SeparatedIsotropicIntersections

/-!
# The actual exterior map, its kernel quotient, and resonance maximality

The original exterior map and the genuine quotient by its actual kernel
give exactly the same isotropic and maximal isotropic subspaces. Thus the
maximal-space cover constructed from the actual resonance definition
connects to separation proved for the original exterior map. Under the
actual separation equalities, every nonzero resonance point has a unique
maximal isotropic space of dimension at least two.

No finiteness of the family, irreducible-component identification,
determinantal scheme reducedness, or topological cup comparison is asserted.
-/

namespace ChenRanks.Resonance

variable {k E W : Type*} [Field k] [AddCommGroup E] [Module k E]
  [AddCommGroup W] [Module k W]

/-- Cup-isotropy for the actual kernel is precisely isotropy for the
original actual exterior map. -/
theorem isCupIsotropic_ker_iff_isIsotropic
    (φ : (⋀[k]^2 E) →ₗ[k] W) (P : Submodule k E) :
    IsCupIsotropic (LinearMap.ker φ) P ↔ IsIsotropic (relationWedge φ) P := by
  rw [isCupIsotropic_iff]
  simp only [LinearMap.mem_ker, IsIsotropic, relationWedge_apply]

/-- Maximality for the genuine kernel quotient and maximality for the
original exterior map coincide by the proved isotropy equivalence. -/
theorem isMaximalIsotropic_kernel_quotient_iff
    (φ : (⋀[k]^2 E) →ₗ[k] W) (P : Submodule k E) :
    IsMaximalIsotropic (relationWedge (cupQuotient (LinearMap.ker φ))) P ↔
      IsMaximalIsotropic (relationWedge φ) P := by
  have hiso : ∀ T : Submodule k E,
      IsIsotropic (relationWedge (cupQuotient (LinearMap.ker φ))) T ↔
        IsIsotropic (relationWedge φ) T := fun T ↦
    (isCupIsotropic_iff_isIsotropic (LinearMap.ker φ) T).symm.trans
      (isCupIsotropic_ker_iff_isIsotropic φ T)
  constructor
  · intro hP
    exact ⟨(hiso P).mp hP.1,
      fun T hPT hT ↦ hP.2 T hPT ((hiso T).mpr hT)⟩
  · intro hP
    exact ⟨(hiso P).mpr hP.1,
      fun T hPT hT ↦ hP.2 T hPT ((hiso T).mp hT)⟩

section FiniteDimension

variable [FiniteDimensional k E]

/-- The actual nonzero resonance witness constructs a maximal isotropic
space for the original exterior map, rather than merely its kernel quotient. -/
theorem nonzero_resonance_mem_original_maximal_isotropic
    (φ : (⋀[k]^2 E) →ₗ[k] W) {a : E} (ha : a ≠ 0)
    (haR : a ∈ resonance (LinearMap.ker φ)) :
    ∃ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P ∧
      2 ≤ Module.finrank k P ∧ a ∈ P := by
  obtain ⟨P, hP, hdimP, haP⟩ :=
    nonzero_resonance_mem_maximal_isotropic (LinearMap.ker φ) ha haR
  exact ⟨P, (isMaximalIsotropic_kernel_quotient_iff φ P).mp hP, hdimP, haP⟩

/-- Pointwise resonance cover expressed using the same original exterior
map to which the geometric separation theorem applies. -/
theorem mem_resonance_ker_iff_zero_or_mem_original_maximal_isotropic
    (φ : (⋀[k]^2 E) →ₗ[k] W) (a : E) :
    a ∈ resonance (LinearMap.ker φ) ↔ a = 0 ∨ ∃ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P ∧
      2 ≤ Module.finrank k P ∧ a ∈ P := by
  rw [mem_resonance_iff_zero_or_mem_maximal_isotropic]
  simp only [isMaximalIsotropic_kernel_quotient_iff]

/-- The actual separation equalities make the maximal isotropic space
containing each nonzero actual resonance point unique. Existence comes from
the proved witness-to-plane and Noetherian-extension constructions. -/
theorem nonzero_resonance_existsUnique_maximal_isotropic_of_separated
    (φ : (⋀[k]^2 E) →ₗ[k] W)
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P → 2 ≤ Module.finrank k P →
        mixedExterior P ⊓ LinearMap.ker φ = pureExterior P)
    {a : E} (ha : a ≠ 0) (haR : a ∈ resonance (LinearMap.ker φ)) :
    ∃! P : Submodule k E,
      IsMaximalIsotropic (relationWedge φ) P ∧
      2 ≤ Module.finrank k P ∧ a ∈ P := by
  obtain ⟨P, hP, hdimP, haP⟩ :=
    nonzero_resonance_mem_original_maximal_isotropic φ ha haR
  refine ⟨P, ⟨hP, hdimP, haP⟩, ?_⟩
  intro Q hQ
  exact (maximalIsotropic_eq_of_nonzero_intersection_of_separated
    φ P Q hP hQ.1 (hsep P hP hdimP) haP hQ.2.2 ha).symm

end FiniteDimension

end ChenRanks.Resonance
