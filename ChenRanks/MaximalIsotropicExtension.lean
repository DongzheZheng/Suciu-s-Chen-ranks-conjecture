import ChenRanks.ResonanceObjects

/-!
# Maximal extension of actual isotropic subspaces

An isotropic subspace in a finite-dimensional vector space has a maximal
isotropic extension. The proof uses the actual ascending-chain condition on
the lattice of submodules. In particular, existence of the extension is not
an input, and finiteness of the set of maximal isotropic subspaces is not a
conclusion.
-/

namespace ChenRanks

variable {k E W : Type*} [Field k]
  [AddCommGroup E] [Module k E] [AddCommGroup W] [Module k W]

/-- The actual Noetherian submodule lattice supplies a maximal isotropic
extension of a given isotropic subspace. -/
theorem exists_maximal_isotropic_extension_of_noetherian
    [IsNoetherian k E] (wedge : E →ₗ[k] E →ₗ[k] W)
    (U : Submodule k E) (hU : IsIsotropic wedge U) :
    ∃ P : Submodule k E, U ≤ P ∧ IsMaximalIsotropic wedge P := by
  obtain ⟨P, hUP, hP⟩ :=
    exists_maximal_ge_of_wellFoundedGT (IsIsotropic wedge) U hU
  exact ⟨P, hUP, hP.1, fun T hPT hT ↦ hP.2 hT hPT⟩

/-- Finite dimensionality of the original vector space implies existence
of a maximal isotropic extension, without choosing an extension in advance. -/
theorem exists_maximal_isotropic_extension
    [FiniteDimensional k E] (wedge : E →ₗ[k] E →ₗ[k] W)
    (U : Submodule k E) (hU : IsIsotropic wedge U) :
    ∃ P : Submodule k E, U ≤ P ∧ IsMaximalIsotropic wedge P := by
  exact exists_maximal_isotropic_extension_of_noetherian wedge U hU

/-- A lower bound on the dimension of the original isotropic subspace is
preserved by the actual maximal extension. -/
theorem exists_maximal_isotropic_extension_finrank_ge
    [FiniteDimensional k E] (wedge : E →ₗ[k] E →ₗ[k] W)
    (U : Submodule k E) (hU : IsIsotropic wedge U)
    (n : ℕ) (hn : n ≤ Module.finrank k U) :
    ∃ P : Submodule k E,
      U ≤ P ∧ IsMaximalIsotropic wedge P ∧ n ≤ Module.finrank k P := by
  obtain ⟨P, hUP, hP⟩ := exists_maximal_isotropic_extension wedge U hU
  exact ⟨P, hUP, hP, hn.trans (Submodule.finrank_mono hUP)⟩

end ChenRanks

namespace ChenRanks.Resonance

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]
  [FiniteDimensional k E]

/-- A genuine cup-isotropic subspace extends to a maximal subspace for
the same genuine exterior quotient. -/
theorem exists_maximal_cup_isotropic_extension
    (I : Submodule k (⋀[k]^2 E)) (U : Submodule k E)
    (hU : IsCupIsotropic I U) :
    ∃ P : Submodule k E, U ≤ P ∧
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P := by
  exact exists_maximal_isotropic_extension (relationWedge (cupQuotient I)) U
    ((isCupIsotropic_iff_isIsotropic I U).mp hU)

/-- The actual maximal extension of a cup-isotropic subspace of dimension
at least two remains contained in the actual resonance point set. -/
theorem exists_maximal_cup_isotropic_extension_subset_resonance
    (I : Submodule k (⋀[k]^2 E)) (U : Submodule k E)
    (hU : IsCupIsotropic I U) (hdim : 2 ≤ Module.finrank k U) :
    ∃ P : Submodule k E, U ≤ P ∧
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P ∧
      2 ≤ Module.finrank k P ∧ (P : Set E) ⊆ resonance I := by
  obtain ⟨P, hUP, hP, hdimP⟩ :=
    exists_maximal_isotropic_extension_finrank_ge
      (relationWedge (cupQuotient I)) U
      ((isCupIsotropic_iff_isIsotropic I U).mp hU) 2 hdim
  refine ⟨P, hUP, hP, hdimP, ?_⟩
  exact isotropic_subspace_subset_resonance I P hdimP
    ((isCupIsotropic_iff_isIsotropic I P).mpr hP.1)

end ChenRanks.Resonance
