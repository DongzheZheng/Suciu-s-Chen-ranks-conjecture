import ChenRanks.IsotropicAdaptedGraphCoordinates
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Actual original equations and their normal-coordinate remainder

The original graph equations are decomposed into their genuine constant,
linear and quadratic polynomials. Original isotropy makes every purely
internal term zero. Each remaining quadratic monomial has a literal
normal variable and another variable vanishing at the actual origin.
Actual separation constructs the original dual equation whose linear part
is each normal variable. These facts prove the two genuine ideal
containments required by Nakayama, and equality after localization at the
actual coordinate origin. No ideal equality or reducedness is an input.

The basis is adapted chart data; construction for every original subspace,
global chart coverage, finite components, and Chen ranks are separate.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicChart

universe u v

variable {k τ : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E] [Fintype τ]

local instance : DecidableEq τ := Classical.decEq τ

private theorem rowDirection_single_same
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (r : Fin 2) (j : τ) :
    rowDirection b r (Pi.single (r, j) 1) = b (Sum.inr j) := by
  classical
  simp [rowDirection, Pi.single_apply, Prod.mk.injEq]

private theorem rowDirection_single_other
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (r s : Fin 2) (hrs : r ≠ s) (j : τ) :
    rowDirection b r (Pi.single (s, j) 1) = 0 := by
  classical
  simp [rowDirection, Prod.mk.injEq, hrs]

private theorem linearRelation_single_zero
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (j : τ) :
    linearRelation I b (Pi.single (0, j) 1) =
      relationWedge (cupQuotient I) (b (Sum.inr j)) (b (Sum.inl 1)) := by
  change relationWedge (cupQuotient I)
      (rowDirection b 0 (Pi.single (0, j) 1)) (b (Sum.inl 1)) +
    relationWedge (cupQuotient I) (b (Sum.inl 0))
      (rowDirection b 1 (Pi.single (0, j) 1)) = _
  rw [rowDirection_single_same, rowDirection_single_other b 1 0 (by decide)]
  simp only [map_zero, add_zero]

private theorem linearRelation_single_one
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (j : τ) :
    linearRelation I b (Pi.single (1, j) 1) =
      relationWedge (cupQuotient I) (b (Sum.inl 0)) (b (Sum.inr j)) := by
  change relationWedge (cupQuotient I)
      (rowDirection b 0 (Pi.single (1, j) 1)) (b (Sum.inl 1)) +
    relationWedge (cupQuotient I) (b (Sum.inl 0))
      (rowDirection b 1 (Pi.single (1, j) 1)) = _
  rw [rowDirection_single_other b 0 1 (by decide), rowDirection_single_same]
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-- The literal linear terms of the original defining polynomial. -/
def linearPolynomial (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (ρ : CupTarget I →ₗ[k] k) :
    CoordinateRing k τ := by
  classical
  exact (∑ j, MvPolynomial.X (0, j) * MvPolynomial.C
      (ρ (relationWedge (cupQuotient I) (b (Sum.inr j)) (b (Sum.inl 1))))) +
    (∑ j, MvPolynomial.X (1, j) * MvPolynomial.C
      (ρ (relationWedge (cupQuotient I) (b (Sum.inl 0)) (b (Sum.inr j)))))

/-- The literal quadratic terms of the original defining polynomial. -/
def quadraticPolynomial (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E) (ρ : CupTarget I →ₗ[k] k) :
    CoordinateRing k τ := by
  classical
  exact ∑ j, ∑ l, MvPolynomial.X (0, j) * MvPolynomial.X (1, l) *
    MvPolynomial.C (ρ (relationWedge (cupQuotient I) (b (Sum.inr j)) (b (Sum.inr l))))

/-- The actual derivative polynomial is precisely the literal linear
    part of the original relation, proved on the genuine coordinate basis. -/
theorem derivativePolynomial_eq_linearPolynomial
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) :
    derivativePolynomial I b ρ = linearPolynomial I b ρ := by
  classical
  unfold derivativePolynomial
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [linearRelation_single_zero, linearRelation_single_one, linearPolynomial]

/-- The actual original equation has exactly its displayed constant,
    derivative and quadratic terms. -/
theorem relationPolynomial_eq_constant_add_derivative_add_quadratic
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ τ) k E)
    (ρ : CupTarget I →ₗ[k] k) :
    relationPolynomial I b ρ =
      MvPolynomial.C (ρ (relationWedge (cupQuotient I)
        (b (Sum.inl 0)) (b (Sum.inl 1)))) +
      derivativePolynomial I b ρ + quadraticPolynomial I b ρ := by
  rw [derivativePolynomial_eq_linearPolynomial]
  unfold relationPolynomial linearPolynomial quadraticPolynomial
  abel

/-- The actual coordinate origin ideal is the kernel of evaluation at zero. -/
def originIdeal (k τ : Type u) [Field k] : Ideal (CoordinateRing k τ) :=
  RingHom.ker (MvPolynomial.aeval (fun _ : Fin 2 × τ ↦ (0 : k))).toRingHom

omit [Fintype τ] in
/-- Constant polynomials prove actual origin evaluation is surjective,
    and hence that its actual kernel is a maximal ideal. -/
instance originIdeal_isMaximal : (originIdeal k τ).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨MvPolynomial.C c, MvPolynomial.aeval_C _ _⟩

omit [Fintype τ] in
/-- Every actual coordinate variable vanishes at the actual origin. -/
theorem X_mem_originIdeal (i : Fin 2 × τ) :
    MvPolynomial.X i ∈ originIdeal k τ := by
  change MvPolynomial.aeval (fun _ : Fin 2 × τ ↦ (0 : k)) (MvPolynomial.X i) = 0
  exact MvPolynomial.aeval_X _ _

section Adapted

variable {μ ν : Type u} [Fintype μ] [Fintype ν]

/-- The actual ideal generated by the literal two-row normal variables. -/
def normalIdeal (k μ ν : Type u) [Field k] : Ideal (CoordinateRing k (μ ⊕ ν)) :=
  Ideal.span (Set.range (fun q : Fin 2 × ν ↦ MvPolynomial.X (q.1, Sum.inr q.2)))

omit [Fintype τ] [Fintype μ] [Fintype ν] in
/-- A literal normal variable belongs to the actual finite-coordinate normal ideal. -/
theorem normal_X_mem_normalIdeal (r : Fin 2) (j : ν) :
    MvPolynomial.X (r, Sum.inr j) ∈ normalIdeal k μ ν :=
  Ideal.subset_span ⟨(r, j), rfl⟩

omit [Fintype τ] [Fintype μ] in
/-- The genuine normal ideal is finitely generated by its finite normal-coordinate set. -/
theorem normalIdeal_fg : (normalIdeal k μ ν).FG :=
  Submodule.fg_span (Set.finite_range _)

omit [Fintype τ] [Fintype μ] [Fintype ν] in
private theorem adapted_relation_zero_of_internal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b)) (x y : E)
    (hx : x ∈ adaptedSubspace b) (hy : y ∈ adaptedSubspace b) :
    relationWedge (cupQuotient I) x y = 0 :=
  (isCupIsotropic_iff_isIsotropic I (adaptedSubspace b)).mp hiso x hx y hy

omit [Fintype τ] in
/-- Original isotropy removes the constant term at the chosen plane. -/
theorem relationPolynomial_eq_derivative_add_quadratic_of_adapted_isotropic
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b)) (ρ : CupTarget I →ₗ[k] k) :
    relationPolynomial I b ρ = derivativePolynomial I b ρ + quadraticPolynomial I b ρ := by
  rw [relationPolynomial_eq_constant_add_derivative_add_quadratic]
  rw [adapted_relation_zero_of_internal I b hiso _ _
    (distinguished_mem_adaptedSubspace b 0) (distinguished_mem_adaptedSubspace b 1)]
  simp only [map_zero, zero_add]

omit [Fintype τ] in
/-- The actual quadratic remainder belongs to the product of the actual
    origin maximal ideal and the actual normal ideal: purely internal
    coefficients vanish by original isotropy. -/
theorem quadraticPolynomial_mem_origin_mul_normal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b)) (ρ : CupTarget I →ₗ[k] k) :
    quadraticPolynomial I b ρ ∈ originIdeal k (μ ⊕ ν) * normalIdeal k μ ν := by
  classical
  unfold quadraticPolynomial
  apply Ideal.sum_mem
  intro j _
  apply Ideal.sum_mem
  intro l _
  rcases j with j | j <;> rcases l with l | l
  · rw [adapted_relation_zero_of_internal I b hiso _ _
      (internal_mem_adaptedSubspace b j) (internal_mem_adaptedSubspace b l)]
    simp only [map_zero, mul_zero]
    exact Ideal.zero_mem _
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (X_mem_originIdeal (0, Sum.inl j)) (normal_X_mem_normalIdeal 1 l))
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul_rev (X_mem_originIdeal (1, Sum.inl l)) (normal_X_mem_normalIdeal 0 j))
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (X_mem_originIdeal (0, Sum.inr j)) (normal_X_mem_normalIdeal 1 l))

omit [Fintype τ] in
/-- The original literal linear terms also lie in the actual normal ideal,
    since all internal direction coefficients vanish by original isotropy. -/
theorem linearPolynomial_mem_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b)) (ρ : CupTarget I →ₗ[k] k) :
    linearPolynomial I b ρ ∈ normalIdeal k μ ν := by
  classical
  unfold linearPolynomial
  apply Ideal.add_mem
  · apply Ideal.sum_mem
    intro j _
    rcases j with j | j
    · rw [adapted_relation_zero_of_internal I b hiso _ _
        (internal_mem_adaptedSubspace b j) (distinguished_mem_adaptedSubspace b 1)]
      simp only [map_zero, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (normal_X_mem_normalIdeal 0 j)
  · apply Ideal.sum_mem
    intro j _
    rcases j with j | j
    · rw [adapted_relation_zero_of_internal I b hiso _ _
        (distinguished_mem_adaptedSubspace b 0) (internal_mem_adaptedSubspace b j)]
      simp only [map_zero, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (normal_X_mem_normalIdeal 1 j)

omit [Fintype τ] in
/-- The actual original relation ideal is contained in the actual normal ideal. -/
theorem relationIdeal_le_normalIdeal_of_adapted_isotropic
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b)) :
    relationIdeal I b ≤ normalIdeal k μ ν := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ⟨ρ, rfl⟩
  rw [relationPolynomial_eq_derivative_add_quadratic_of_adapted_isotropic I b hiso,
    derivativePolynomial_eq_linearPolynomial]
  apply Ideal.add_mem
  · exact linearPolynomial_mem_normalIdeal I b hiso ρ
  · exact Ideal.mul_le_left (quadraticPolynomial_mem_origin_mul_normal I b hiso ρ)

omit [Fintype τ] in
/-- The actual original equations internally generate every normal variable
    modulo the actual product of origin and normal ideals. -/
theorem normalIdeal_le_relationIdeal_sup_origin_mul_normal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b))
    (hsep : mixedExterior (adaptedSubspace b) ⊓ I = pureExterior (adaptedSubspace b)) :
    normalIdeal k μ ν ≤ relationIdeal I b ⊔ originIdeal k (μ ⊕ ν) * normalIdeal k μ ν := by
  rw [normalIdeal, Ideal.span_le]
  rintro _ ⟨⟨r, j⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ := exists_cup_dual_derivativePolynomial_eq_normal_X I b hsep r j
  have hp : relationPolynomial I b ρ ∈ relationIdeal I b :=
    Ideal.subset_span (Set.mem_range_self ρ)
  rw [relationPolynomial_eq_derivative_add_quadratic_of_adapted_isotropic I b hiso, hρ] at hp
  have hp' := (le_sup_left : relationIdeal I b ≤
    relationIdeal I b ⊔ originIdeal k (μ ⊕ ν) * normalIdeal k μ ν) hp
  have hq := (le_sup_right : originIdeal k (μ ⊕ ν) * normalIdeal k μ ν ≤
    relationIdeal I b ⊔ originIdeal k (μ ⊕ ν) * normalIdeal k μ ν)
    (quadraticPolynomial_mem_origin_mul_normal I b hiso ρ)
  simpa only [add_sub_cancel_right] using
    (relationIdeal I b ⊔ originIdeal k (μ ⊕ ν) * normalIdeal k μ ν).sub_mem hp' hq

omit [Fintype τ] in
/-- Nakayama proves the actual localized original relation ideal equals
    the actual localized normal ideal at the genuine coordinate origin.
    Both requisite ideal containments and finite generation have been
    derived from the original isotropy and separation. -/
theorem localized_relationIdeal_eq_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b))
    (hsep : mixedExterior (adaptedSubspace b) ⊓ I = pureExterior (adaptedSubspace b)) :
    Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν))
      (Localization.AtPrime (originIdeal k (μ ⊕ ν)))) (relationIdeal I b) =
    Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν))
      (Localization.AtPrime (originIdeal k (μ ⊕ ν)))) (normalIdeal k μ ν) := by
  let R := CoordinateRing k (μ ⊕ ν)
  let m : Ideal R := originIdeal k (μ ⊕ ν)
  let A := Localization.AtPrime m
  let f : R →+* A := algebraMap R A
  have hforward : Ideal.map f (relationIdeal I b) ≤ Ideal.map f (normalIdeal k μ ν) :=
    Ideal.map_mono (relationIdeal_le_normalIdeal_of_adapted_isotropic I b hiso)
  have hmod : Ideal.map f (normalIdeal k μ ν) ≤
      Ideal.map f (relationIdeal I b ⊔ originIdeal k (μ ⊕ ν) * normalIdeal k μ ν) :=
    Ideal.map_mono (normalIdeal_le_relationIdeal_sup_origin_mul_normal I b hiso hsep)
  rw [Ideal.map_sup, Ideal.map_mul] at hmod
  have hm : Ideal.map f (originIdeal k (μ ⊕ ν)) = IsLocalRing.maximalIdeal A :=
    Localization.AtPrime.map_eq_maximalIdeal
  rw [hm] at hmod
  have hfg : (Ideal.map f (normalIdeal k μ ν)).FG :=
    (normalIdeal_fg (k := k) (μ := μ) (ν := ν)).map f
  apply le_antisymm hforward
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  simpa only [Ideal.smul_eq_mul] using hmod

end Adapted

end ChenRanks.Resonance.IsotropicChart
