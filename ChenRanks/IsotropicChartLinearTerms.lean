import ChenRanks.IsotropicGraphChartTangent
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The actual linear relation on the original graph chart

The first-order relation is a genuine linear map into the original cup
quotient. Actual exterior separation identifies its kernel with the
coordinate directions whose two actual graph vectors lie in P. Every
actual linear form annihilating P consequently factors through this
relation. The factor is constructed by the dual-map range theorem; it
is not an input normal-direction detector.

Local ideal equality, adapted coordinates and reducedness remain separate
steps. No scheme-theoretic conclusion follows merely from these linear
identities.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicChart

universe u v

variable {k τ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E] [Fintype τ]

/-- An actual row of graph-coordinate directions, as a linear map to
    the original vector space. -/
def rowDirection (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (r : Fin 2) :
    (Fin 2 × τ → k) →ₗ[k] E where
  toFun t := ∑ j, t (r, j) • b (Sum.inr j)
  map_add' t s := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul, RingHom.id_apply]

@[simp] theorem rowDirection_zero
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (t : Fin 2 × τ → k) :
    rowDirection b 0 t = tangentFirst b t := rfl

@[simp] theorem rowDirection_one
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (t : Fin 2 × τ → k) :
    rowDirection b 1 t = tangentSecond b t := rfl

/-- The genuine derivative of the original cup relation on the graph chart. -/
def linearRelation (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) :
    (Fin 2 × τ → k) →ₗ[k] CupTarget I :=
  ((relationWedge (cupQuotient I)).flip (b (Sum.inl 1))).comp (rowDirection b 0) +
    ((relationWedge (cupQuotient I)) (b (Sum.inl 0))).comp (rowDirection b 1)

@[simp] theorem linearRelation_apply
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (t : Fin 2 × τ → k) :
    linearRelation I b t =
      relationWedge (cupQuotient I) (tangentFirst b t) (b (Sum.inl 1)) +
        relationWedge (cupQuotient I) (b (Sum.inl 0)) (tangentSecond b t) := rfl

/-- The linear relation is the actual square-zero coefficient of each
    genuine chart equation. -/
theorem aeval_relationPolynomial_infinitesimal_snd_eq_linearRelation
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (t : Fin 2 × τ → k) :
    (MvPolynomial.aeval (infinitesimalCoordinates t) (relationPolynomial I b ρ)).snd =
      ρ (linearRelation I b t) :=
  aeval_relationPolynomial_infinitesimal_snd I b ρ t

omit [Fintype τ] in
private theorem distinguished_pair_linearIndependent
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) :
    LinearIndependent k ![b (Sum.inl 0), b (Sum.inl 1)] := by
  have hfun : ![b (Sum.inl 0), b (Sum.inl 1)] =
      (fun i : Fin 2 ↦ b (Sum.inl i)) := by
    funext i
    fin_cases i <;> rfl
  rw [hfun]
  exact b.linearIndependent.comp (Sum.inl : Fin 2 → Fin 2 ⊕ τ) Sum.inl_injective

/-- Actual separation eliminates both normal directions from the actual
    derivative kernel. -/
theorem directions_mem_of_linearRelation_eq_zero
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (P : Submodule k E) (hsep : mixedExterior P ⊓ I = pureExterior P)
    (hu : b (Sum.inl 0) ∈ P) (hv : b (Sum.inl 1) ∈ P)
    (t : Fin 2 × τ → k) (ht : linearRelation I b t = 0) :
    tangentFirst b t ∈ P ∧ tangentSecond b t ∈ P := by
  have hrel : exteriorWedge (k := k) (tangentFirst b t) (b (Sum.inl 1)) +
      exteriorWedge (b (Sum.inl 0)) (tangentSecond b t) ∈ I := by
    apply (cupQuotient_eq_zero_iff I _).mp
    simpa only [linearRelation_apply, relationWedge_apply, map_add] using ht
  exact tangent_representatives_mem_of_separated_relation I P hsep
    (b (Sum.inl 0)) (b (Sum.inl 1)) (tangentFirst b t) (tangentSecond b t)
    hu hv (distinguished_pair_linearIndependent b) hrel

/-- Conversely, genuine directions inside an original isotropic P give
    zero actual linear relation. -/
theorem linearRelation_eq_zero_of_directions_mem
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (P : Submodule k E) (hiso : IsCupIsotropic I P)
    (hu : b (Sum.inl 0) ∈ P) (hv : b (Sum.inl 1) ∈ P)
    (t : Fin 2 × τ → k) (hfirst : tangentFirst b t ∈ P)
    (hsecond : tangentSecond b t ∈ P) : linearRelation I b t = 0 := by
  have h₀ := (isCupIsotropic_iff_isIsotropic I P).mp hiso
    (tangentFirst b t) hfirst (b (Sum.inl 1)) hv
  have h₁ := (isCupIsotropic_iff_isIsotropic I P).mp hiso
    (b (Sum.inl 0)) hu (tangentSecond b t) hsecond
  simp only [linearRelation_apply, h₀, h₁, add_zero]

/-- The exact derivative kernel is obtained from original isotropy and
    original exterior separation, rather than prescribed as a definition. -/
theorem mem_ker_linearRelation_iff_directions_mem
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (P : Submodule k E) (hiso : IsCupIsotropic I P)
    (hsep : mixedExterior P ⊓ I = pureExterior P)
    (hu : b (Sum.inl 0) ∈ P) (hv : b (Sum.inl 1) ∈ P) (t : Fin 2 × τ → k) :
    t ∈ LinearMap.ker (linearRelation I b) ↔
      tangentFirst b t ∈ P ∧ tangentSecond b t ∈ P := by
  constructor
  · intro ht
    exact directions_mem_of_linearRelation_eq_zero I b P hsep hu hv t ht
  · rintro ⟨hfirst, hsecond⟩
    exact linearRelation_eq_zero_of_directions_mem I b P hiso hu hv t hfirst hsecond

/-- Every true linear form annihilating P, on either coordinate row,
    is the dual of the actual derivative relation. The actual dual form
    on the cup target is constructed from the proved kernel inclusion. -/
theorem exists_cup_dual_for_annihilating_row
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (P : Submodule k E) (hsep : mixedExterior P ⊓ I = pureExterior P)
    (hu : b (Sum.inl 0) ∈ P) (hv : b (Sum.inl 1) ∈ P)
    (ℓ : E →ₗ[k] k) (hℓ : ℓ ∈ P.dualAnnihilator) (r : Fin 2) :
    ∃ ρ : CupTarget I →ₗ[k] k,
      ρ.comp (linearRelation I b) = ℓ.comp (rowDirection b r) := by
  have hvanish : ℓ.comp (rowDirection b r) ∈
      (LinearMap.ker (linearRelation I b)).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro t ht
    have hmem := directions_mem_of_linearRelation_eq_zero I b P hsep hu hv t ht
    apply (Submodule.mem_dualAnnihilator (W := P) ℓ).mp hℓ
    fin_cases r
    · exact hmem.1
    · exact hmem.2
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hvanish
  obtain ⟨ρ, hρ⟩ := hvanish
  exact ⟨ρ, hρ⟩

end ChenRanks.Resonance.IsotropicChart
