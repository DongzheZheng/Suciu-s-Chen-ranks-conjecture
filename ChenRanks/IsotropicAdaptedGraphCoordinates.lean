import ChenRanks.IsotropicChartLinearTerms
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Normal coordinates in an adapted graph chart

A finite basis splits the ambient space into internal and normal
directions. The internal span is the subspace `P`, and the normal
coordinate forms annihilate it. Separation constructs cup-target
functionals whose linear relations are precisely the normal coordinates.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicChart

universe u v

variable {k μ ν : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [Fintype μ] [Fintype ν]

/-- Actual indices of the two distinguished vectors and all chosen
    internal complementary vectors. -/
def internalIndices : Set (Fin 2 ⊕ (μ ⊕ ν)) :=
  {i | ∀ j : ν, i ≠ Sum.inr (Sum.inr j)}

/-- The actual original-vector-space span of the internal basis vectors. -/
def adaptedSubspace (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E) : Submodule k E :=
  Submodule.span k (b '' (internalIndices : Set (Fin 2 ⊕ (μ ⊕ ν))))

/-- A literal normal-coordinate form of the actual full basis. -/
abbrev normalCoordinate (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E) (j : ν) :
    E →ₗ[k] k := b.coord (Sum.inr (Sum.inr j))

omit [Fintype μ] [Fintype ν] in
/-- The actual distinguished vectors are inside the actual internal span. -/
theorem distinguished_mem_adaptedSubspace
    (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E) (r : Fin 2) :
    b (Sum.inl r) ∈ adaptedSubspace b := by
  apply Submodule.subset_span
  refine ⟨Sum.inl r, ?_, rfl⟩
  simp [internalIndices]

omit [Fintype μ] [Fintype ν] in
/-- The actual chosen internal complementary basis vectors lie in P. -/
theorem internal_mem_adaptedSubspace
    (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E) (i : μ) :
    b (Sum.inr (Sum.inl i)) ∈ adaptedSubspace b := by
  apply Submodule.subset_span
  refine ⟨Sum.inr (Sum.inl i), ?_, rfl⟩
  simp [internalIndices]

omit [Fintype μ] [Fintype ν] in
/-- The true basis coordinate form vanishes on the entire actual P,
    proved through the genuine finite-support basis representation. -/
theorem normalCoordinate_mem_dualAnnihilator
    (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E) (j : ν) :
    normalCoordinate b j ∈ (adaptedSubspace b).dualAnnihilator := by
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro p hp
  change b.repr p (Sum.inr (Sum.inr j)) = 0
  by_contra hnonzero
  have hs := b.repr_support_subset_of_mem_span internalIndices hp
  have hi : Sum.inr (Sum.inr j) ∈ (b.repr p).support :=
    Finsupp.mem_support_iff.mpr hnonzero
  exact hs hi j rfl

/-- Applying the actual normal-coordinate form to a genuine coordinate
    row retrieves precisely the original literal normal scalar. -/
@[simp] theorem normalCoordinate_rowDirection
    (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (j : ν) (r : Fin 2) (t : Fin 2 × (μ ⊕ ν) → k) :
    normalCoordinate b j (rowDirection b r t) = t (r, Sum.inr j) := by
  classical
  change b.coord (Sum.inr (Sum.inr j))
    (∑ i : μ ⊕ ν, t (r, i) • b (Sum.inr i)) = t (r, Sum.inr j)
  rw [map_sum]
  simp only [map_smul]
  simp [_root_.Module.Basis.coord_apply, Finsupp.single_apply]

/-- Actual separation constructs the genuine cup-target dual form for
    each literal normal coordinate of either row. -/
theorem exists_cup_dual_for_normal_coordinate
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hsep : mixedExterior (adaptedSubspace b) ⊓ I = pureExterior (adaptedSubspace b))
    (r : Fin 2) (j : ν) :
    ∃ ρ : CupTarget I →ₗ[k] k, ∀ t : Fin 2 × (μ ⊕ ν) → k,
      ρ (linearRelation I b t) = t (r, Sum.inr j) := by
  obtain ⟨ρ, hρ⟩ := exists_cup_dual_for_annihilating_row I b (adaptedSubspace b)
    hsep (distinguished_mem_adaptedSubspace b 0)
    (distinguished_mem_adaptedSubspace b 1) (normalCoordinate b j)
    (normalCoordinate_mem_dualAnnihilator b j) r
  refine ⟨ρ, ?_⟩
  intro t
  have h := DFunLike.congr_fun hρ t
  simpa only [LinearMap.comp_apply, normalCoordinate_rowDirection] using h

/-- The actual degree-one polynomial associated with the original
    derivative, by its values on the genuine coordinate basis vectors. -/
def derivativePolynomial {τ : Type u} [Fintype τ]
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) : CoordinateRing k τ := by
  classical
  exact ∑ i : Fin 2 × τ, MvPolynomial.X i *
    MvPolynomial.C (ρ (linearRelation I b (Pi.single i 1)))

omit [Fintype μ] [Fintype ν] in
/-- A proved factorization through the actual derivative identifies its
    genuine degree-one polynomial with the literal coordinate variable. -/
theorem derivativePolynomial_eq_X_of_coordinate_factor {τ : Type u} [Fintype τ]
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (q : Fin 2 × τ)
    (hρ : ∀ t : Fin 2 × τ → k, ρ (linearRelation I b t) = t q) :
    derivativePolynomial I b ρ = MvPolynomial.X q := by
  classical
  simp only [derivativePolynomial]
  simp_rw [hρ]
  simp [Pi.single_apply]

/-- Each actual literal normal variable is generated as a genuine linear
    part of an original cup-dual equation, using actual separation. -/
theorem exists_cup_dual_derivativePolynomial_eq_normal_X
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hsep : mixedExterior (adaptedSubspace b) ⊓ I = pureExterior (adaptedSubspace b))
    (r : Fin 2) (j : ν) :
    ∃ ρ : CupTarget I →ₗ[k] k,
      derivativePolynomial I b ρ = MvPolynomial.X (r, Sum.inr j) := by
  obtain ⟨ρ, hρ⟩ := exists_cup_dual_for_normal_coordinate I b hsep r j
  exact ⟨ρ, derivativePolynomial_eq_X_of_coordinate_factor I b ρ (r, Sum.inr j) hρ⟩

end ChenRanks.Resonance.IsotropicChart
