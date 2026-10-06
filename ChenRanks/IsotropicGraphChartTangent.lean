import ChenRanks.IsotropicGrassmannianChart
import ChenRanks.SeparatedIsotropicTangentDirections
import Mathlib.Algebra.DualNumber

/-!
# Actual dual-number points of the original isotropic graph chart

Pure infinitesimal coordinates are actual dual numbers. Factoring their
actual polynomial evaluation through the genuine original chart ideal
implies both the original constant exterior relation and its true linear
term. Actual separation then forces the two graph directions into P.

These statements concern the actual affine chart and actual dual-number
morphisms. Global Grassmannian gluing, local ideal equality and reducedness
are not assumed or concluded.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicChart

universe u v

variable {k τ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E] [Fintype τ]

/-- Actual pure dual-number coordinates, using the genuine square-zero
ideal of the dual-number ring. -/
def infinitesimalCoordinates (t : Fin 2 × τ → k) (i : Fin 2 × τ) : DualNumber k :=
  TrivSqZeroExt.inr (t i)

/-- The first genuine graph direction in the original vector space. -/
def tangentFirst (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (t : Fin 2 × τ → k) : E :=
  ∑ j, t (0, j) • b (Sum.inr j)

/-- The second genuine graph direction in the original vector space. -/
def tangentSecond (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (t : Fin 2 × τ → k) : E :=
  ∑ j, t (1, j) • b (Sum.inr j)

/-- Genuine factorization through the actual original chart quotient.
The hypothesis is precisely that the actual ring evaluation descends. -/
def dualPoint (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (t : Fin 2 × τ → k)
    (hIdeal : relationIdeal I b ≤
      RingHom.ker (MvPolynomial.aeval (infinitesimalCoordinates t)).toRingHom) :
    (CoordinateRing k τ ⧸ relationIdeal I b) →ₐ[k] DualNumber k :=
  Ideal.Quotient.liftₐ (relationIdeal I b)
    (MvPolynomial.aeval (infinitesimalCoordinates t)) hIdeal

/-- The corresponding actual affine scheme morphism from the spectrum
of the dual-number ring to the original chart scheme. -/
def dualPointMorphism (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (t : Fin 2 × τ → k)
    (hIdeal : relationIdeal I b ≤
      RingHom.ker (MvPolynomial.aeval (infinitesimalCoordinates t)).toRingHom) :
    Spec (.of (DualNumber k)) ⟶ scheme I b :=
  Spec.map (CommRingCat.ofHom (dualPoint I b t hIdeal).toRingHom)

/-- The scalar part of a true dual-number relation is the original
constant exterior relation. -/
theorem aeval_relationPolynomial_infinitesimal_fst
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (t : Fin 2 × τ → k) :
    (MvPolynomial.aeval (infinitesimalCoordinates t) (relationPolynomial I b ρ)).fst =
      ρ (relationWedge (cupQuotient I) (b (Sum.inl 0)) (b (Sum.inl 1))) := by
  classical
  simp [relationPolynomial, infinitesimalCoordinates, TrivSqZeroExt.fst_sum,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- The square-zero part of a true dual-number relation is its actual
linear exterior term. The quadratic directions vanish because ε² is zero. -/
theorem aeval_relationPolynomial_infinitesimal_snd
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) (t : Fin 2 × τ → k) :
    (MvPolynomial.aeval (infinitesimalCoordinates t) (relationPolynomial I b ρ)).snd =
      ρ (relationWedge (cupQuotient I) (tangentFirst b t) (b (Sum.inl 1)) +
        relationWedge (cupQuotient I) (b (Sum.inl 0)) (tangentSecond b t)) := by
  classical
  simp [relationPolynomial, infinitesimalCoordinates, tangentFirst, tangentSecond,
    TrivSqZeroExt.snd_sum, TrivSqZeroExt.algebraMap_eq_inl,
    map_add, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]

private theorem cupTarget_eq_zero_of_duals
    (I : Submodule k (⋀[k]^2 E)) (z : CupTarget I)
    (hz : ∀ ρ : CupTarget I →ₗ[k] k, ρ z = 0) : z = 0 := by
  by_contra hzero
  obtain ⟨ρ, hρ⟩ := _root_.Module.Projective.exists_dual_ne_zero k hzero
  exact hρ (hz ρ)

/-- Actual factorization of the infinitesimal coordinate evaluation
forces both actual original-relation vectors to vanish. The original
dual forms detect them by a proved vector-space theorem. -/
theorem constant_and_linear_relation_of_infinitesimal_chart_equations
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (t : Fin 2 × τ → k)
    (hIdeal : relationIdeal I b ≤
      RingHom.ker (MvPolynomial.aeval (infinitesimalCoordinates t)).toRingHom) :
    relationWedge (cupQuotient I) (b (Sum.inl 0)) (b (Sum.inl 1)) = 0 ∧
      relationWedge (cupQuotient I) (tangentFirst b t) (b (Sum.inl 1)) +
        relationWedge (cupQuotient I) (b (Sum.inl 0)) (tangentSecond b t) = 0 := by
  have hscalar : ∀ ρ : CupTarget I →ₗ[k] k,
      MvPolynomial.aeval (infinitesimalCoordinates t) (relationPolynomial I b ρ) = 0 := by
    intro ρ
    exact hIdeal (Ideal.subset_span (Set.mem_range_self ρ))
  constructor
  · apply cupTarget_eq_zero_of_duals I
    intro ρ
    have h := congrArg (fun z : DualNumber k ↦ z.fst) (hscalar ρ)
    change TrivSqZeroExt.fst
      (MvPolynomial.aeval (infinitesimalCoordinates t) (relationPolynomial I b ρ)) =
        TrivSqZeroExt.fst (0 : DualNumber k) at h
    rw [aeval_relationPolynomial_infinitesimal_fst, TrivSqZeroExt.fst_zero] at h
    exact h
  · apply cupTarget_eq_zero_of_duals I
    intro ρ
    have h := congrArg (fun z : DualNumber k ↦ z.snd) (hscalar ρ)
    change TrivSqZeroExt.snd
      (MvPolynomial.aeval (infinitesimalCoordinates t) (relationPolynomial I b ρ)) =
        TrivSqZeroExt.snd (0 : DualNumber k) at h
    rw [aeval_relationPolynomial_infinitesimal_snd, TrivSqZeroExt.snd_zero] at h
    exact h

/-- The two genuine graph directions of an actual infinitesimal chart
point lie in P under the actual exterior separation equality. -/
theorem tangentDirections_mem_of_actual_dual_chart_point
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (P : Submodule k E) (hsep : mixedExterior P ⊓ I = pureExterior P)
    (hu : b (Sum.inl 0) ∈ P) (hv : b (Sum.inl 1) ∈ P)
    (t : Fin 2 × τ → k)
    (hIdeal : relationIdeal I b ≤
      RingHom.ker (MvPolynomial.aeval (infinitesimalCoordinates t)).toRingHom) :
    tangentFirst b t ∈ P ∧ tangentSecond b t ∈ P := by
  have huv : LinearIndependent k ![b (Sum.inl 0), b (Sum.inl 1)] := by
    have hfun : ![b (Sum.inl 0), b (Sum.inl 1)] =
        (fun i : Fin 2 ↦ b (Sum.inl i)) := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    exact b.linearIndependent.comp (Sum.inl : Fin 2 → Fin 2 ⊕ τ) Sum.inl_injective
  have hlinear :=
    (constant_and_linear_relation_of_infinitesimal_chart_equations I b t hIdeal).2
  have hrel : exteriorWedge (k := k) (tangentFirst b t) (b (Sum.inl 1)) +
      exteriorWedge (b (Sum.inl 0)) (tangentSecond b t) ∈ I := by
    apply (cupQuotient_eq_zero_iff I _).mp
    simpa only [map_add, relationWedge_apply] using hlinear
  exact tangent_representatives_mem_of_separated_relation I P hsep
    (b (Sum.inl 0)) (b (Sum.inl 1)) (tangentFirst b t) (tangentSecond b t)
    hu hv huv hrel

end ChenRanks.Resonance.IsotropicChart
