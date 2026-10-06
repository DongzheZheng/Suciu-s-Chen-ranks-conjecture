import ChenRanks.KoszulPointContraction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Separated maximal isotropic spaces have trivial intersections

This is the intersection argument in the paper's finite-components
proposition. A true exterior contraction shows that a nonzero vector
in P cannot wedge with a vector outside P into the actual exterior
square of P. Consequently two maximal isotropic spaces, one satisfying
the actual separation equality, cannot share a nonzero vector.

This is linear algebra after geometric separation; it makes no claim
that the actual resonance scheme has already been constructed or shown
reduced, or that its irreducible components have been counted.
-/

noncomputable section

namespace ChenRanks

variable {k E W : Type*} [Field k] [AddCommGroup E] [Module k E]
  [AddCommGroup W] [Module k W]

/-- The actual exterior contraction preserves the actual exterior
square of a subspace. -/
theorem pointContraction_pureExterior_mem
    (P : Submodule k E) (ρ : E →ₗ[k] k) {z : ⋀[k]^2 E}
    (hz : z ∈ pureExterior P) : Koszul.pointDeltaTwo k E ρ z ∈ P := by
  have hle : pureExterior P ≤ P.comap (Koszul.pointDeltaTwo k E ρ) := by
    rw [pureExterior_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, q, rfl⟩
    change Koszul.pointDeltaTwo k E ρ (exteriorWedge (p : E) (q : E)) ∈ P
    rw [Koszul.pointDeltaTwo_wedge]
    exact P.sub_mem (P.smul_mem _ q.property) (P.smul_mem _ p.property)
  exact hle hz

/-- Wedge membership in the actual pure exterior square forces the
second factor into P when the first factor is nonzero in P. -/
theorem mem_subspace_of_nonzero_wedge_mem_pureExterior
    (P : Submodule k E) {a g : E} (ha : a ∈ P) (ha0 : a ≠ 0)
    (hag : exteriorWedge (k := k) a g ∈ pureExterior P) : g ∈ P := by
  obtain ⟨ρ, hρ⟩ := _root_.Module.Projective.exists_dual_eq_one k ha0
  have h := pointContraction_pureExterior_mem P ρ hag
  rw [Koszul.pointDeltaTwo_wedge, hρ, one_smul] at h
  have ht := P.add_mem h (P.smul_mem (ρ g) ha)
  simpa only [sub_add_cancel] using ht

/-- A shared nonzero vector identifies the two actual maximal isotropic
subspaces once the actual separation equality is proved. -/
theorem maximalIsotropic_eq_of_nonzero_intersection_of_separated
    (φ : ⋀[k]^2 E →ₗ[k] W) (P Q : Submodule k E)
    (hP : IsMaximalIsotropic (relationWedge φ) P)
    (hQ : IsMaximalIsotropic (relationWedge φ) Q)
    (hsep : mixedExterior P ⊓ LinearMap.ker φ = pureExterior P)
    {a : E} (haP : a ∈ P) (haQ : a ∈ Q) (ha0 : a ≠ 0) : P = Q := by
  have hQP : Q ≤ P := by
    intro g hg
    have hag : exteriorWedge (k := k) a g ∈ pureExterior P := by
      rw [← hsep]
      exact ⟨exteriorWedge_mem_mixed P ⟨a, haP⟩ g, hQ.1 a haQ g hg⟩
    exact mem_subspace_of_nonzero_wedge_mem_pureExterior P haP ha0 hag
  exact le_antisymm (hQ.2 P hQP hP.1) hQP

/-- Distinct actual maximal isotropic subspaces have zero intersection.
Finiteness and scheme reducedness require the subsequent geometric proof. -/
theorem maximalIsotropic_inf_eq_bot_of_ne_of_separated
    (φ : ⋀[k]^2 E →ₗ[k] W) (P Q : Submodule k E)
    (hP : IsMaximalIsotropic (relationWedge φ) P)
    (hQ : IsMaximalIsotropic (relationWedge φ) Q)
    (hsep : mixedExterior P ⊓ LinearMap.ker φ = pureExterior P)
    (hne : P ≠ Q) : P ⊓ Q = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  change a = 0
  by_contra ha0
  exact hne (maximalIsotropic_eq_of_nonzero_intersection_of_separated
    φ P Q hP hQ hsep ha.1 ha.2 ha0)

end ChenRanks
