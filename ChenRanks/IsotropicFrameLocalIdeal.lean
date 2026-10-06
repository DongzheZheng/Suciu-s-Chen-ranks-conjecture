import ChenRanks.IsotropicFrameLinearTerms
import ChenRanks.LocalIdealEqualityNeighborhood

/-!
# Local normal equations for ordered frames

A finite adapted basis splits the ambient space into internal and normal
directions. The center is an independent pair in the internal subspace.
Isotropy eliminates the internal quadratic coefficients; each remaining
monomial contains an origin variable and a normal variable. The complete
frame derivative supplies the normal variables by dual-map factorization.
The resulting ideal containments yield a principal neighborhood by
Nakayama's lemma.

The cup map in this module is the quotient by the exterior relation
subspace `I`.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k μ ν : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [Fintype μ] [Fintype ν]

/-- The actual original span of the internal vectors in a split full basis. -/
def internalSubspace (b : _root_.Module.Basis (μ ⊕ ν) k E) : Submodule k E :=
  Submodule.span k (b '' Set.range (Sum.inl : μ → μ ⊕ ν))

/-- A genuine normal-coordinate linear form in the split full basis. -/
abbrev splitNormalCoordinate (b : _root_.Module.Basis (μ ⊕ ν) k E) (j : ν) :
    E →ₗ[k] k := b.coord (Sum.inr j)

omit [Fintype μ] [Fintype ν] in
/-- Every actual internal basis vector lies in its actual internal span. -/
theorem internalBasis_mem_internalSubspace
    (b : _root_.Module.Basis (μ ⊕ ν) k E) (j : μ) :
    b (Sum.inl j) ∈ internalSubspace b :=
  Submodule.subset_span ⟨Sum.inl j, ⟨j, rfl⟩, rfl⟩

omit [Fintype μ] [Fintype ν] in
/-- The actual normal basis coordinate vanishes on the entire internal
span, proved from genuine basis representation support. -/
theorem splitNormalCoordinate_mem_dualAnnihilator
    (b : _root_.Module.Basis (μ ⊕ ν) k E) (j : ν) :
    splitNormalCoordinate b j ∈ (internalSubspace b).dualAnnihilator := by
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro p hp
  change b.repr p (Sum.inr j) = 0
  by_contra hnonzero
  have hs := b.repr_support_subset_of_mem_span
    (Set.range (Sum.inl : μ → μ ⊕ ν)) hp
  have hi : Sum.inr j ∈ (b.repr p).support :=
    Finsupp.mem_support_iff.mpr hnonzero
  obtain ⟨i, h⟩ := hs hi
  cases h

omit [Fintype μ] [Fintype ν] in
private theorem split_relation_zero_of_internal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b)) (x y : E)
    (hx : x ∈ internalSubspace b) (hy : y ∈ internalSubspace b) :
    relationWedge (cupQuotient I) x y = 0 :=
  (isCupIsotropic_iff_isIsotropic I (internalSubspace b)).mp hiso x hx y hy

/-- The actual complete quadratic frame relation lies in the true origin
ideal times the true finite normal-coordinate ideal. -/
theorem fullQuadratic_mem_origin_mul_normal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b)) (ρ : CupTarget I →ₗ[k] k) :
    relationPolynomial I b ρ ∈
      IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν := by
  classical
  unfold relationPolynomial
  apply Ideal.sum_mem
  intro j _
  apply Ideal.sum_mem
  intro l _
  rcases j with j | j <;> rcases l with l | l
  · rw [split_relation_zero_of_internal I b hiso _ _
      (internalBasis_mem_internalSubspace b j) (internalBasis_mem_internalSubspace b l)]
    simp only [map_zero, mul_zero]
    exact Ideal.zero_mem _
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (IsotropicChart.X_mem_originIdeal (0, Sum.inl j))
        (IsotropicChart.normal_X_mem_normalIdeal 1 l))
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul_rev (IsotropicChart.X_mem_originIdeal (1, Sum.inl l))
        (IsotropicChart.normal_X_mem_normalIdeal 0 j))
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (IsotropicChart.X_mem_originIdeal (0, Sum.inr j))
        (IsotropicChart.normal_X_mem_normalIdeal 1 l))

/-- The complete linear term has no internal coefficient, because the
actual center and all actual internal directions lie in the isotropic span. -/
theorem centeredLinearPolynomial_mem_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b)) (c : Fin 2 → E)
    (hc₀ : c 0 ∈ internalSubspace b) (hc₁ : c 1 ∈ internalSubspace b)
    (ρ : CupTarget I →ₗ[k] k) :
    centeredLinearPolynomial I b c ρ ∈ IsotropicChart.normalIdeal k μ ν := by
  classical
  unfold centeredLinearPolynomial
  apply Ideal.add_mem
  · apply Ideal.sum_mem
    intro j _
    rcases j with j | j
    · rw [split_relation_zero_of_internal I b hiso _ _
        (internalBasis_mem_internalSubspace b j) hc₁]
      simp only [map_zero, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (IsotropicChart.normal_X_mem_normalIdeal 0 j)
  · apply Ideal.sum_mem
    intro j _
    rcases j with j | j
    · rw [split_relation_zero_of_internal I b hiso _ _
        hc₀ (internalBasis_mem_internalSubspace b j)]
      simp only [map_zero, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (IsotropicChart.normal_X_mem_normalIdeal 1 j)

/-- True centered original frame equations are contained in the genuine
normal ideal, with the actual constant term eliminated by original isotropy. -/
theorem centeredRelationIdeal_le_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b)) (c : Fin 2 → E)
    (hc₀ : c 0 ∈ internalSubspace b) (hc₁ : c 1 ∈ internalSubspace b) :
    centeredRelationIdeal I b c ≤ IsotropicChart.normalIdeal k μ ν := by
  rw [centeredRelationIdeal, Ideal.span_le]
  rintro _ ⟨ρ, rfl⟩
  rw [centeredRelationPolynomial_of_center_relation_zero I b c ρ
    (split_relation_zero_of_internal I b hiso _ _ hc₀ hc₁)]
  apply Ideal.add_mem
  · exact centeredLinearPolynomial_mem_normalIdeal I b hiso c hc₀ hc₁ ρ
  · exact Ideal.mul_le_left (fullQuadratic_mem_origin_mul_normal I b hiso ρ)

section InfiniteField

variable [Infinite k]

/-- Each literal normal variable arises from a constructed true cup
dual for the complete derivative, without a prescribed normal detector. -/
theorem exists_cup_dual_centeredLinearPolynomial_eq_split_normal_X
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hsep : mixedExterior (internalSubspace b) ⊓ I = pureExterior (internalSubspace b))
    (c : Fin 2 → E) (hc₀ : c 0 ∈ internalSubspace b)
    (hc₁ : c 1 ∈ internalSubspace b) (hpair : LinearIndependent k ![c 0, c 1])
    (r : Fin 2) (j : ν) :
    ∃ ρ : CupTarget I →ₗ[k] k,
      centeredLinearPolynomial I b c ρ = MvPolynomial.X (r, Sum.inr j) :=
  exists_cup_dual_centeredLinearPolynomial_eq_normal_X I (internalSubspace b)
    hsep b c hc₀ hc₁ hpair r (Sum.inr j)
    (splitNormalCoordinate_mem_dualAnnihilator b j)

/-- The actual complete frame equations generate every normal variable
modulo the product of the true origin and normal ideals. -/
theorem normalIdeal_le_centeredRelationIdeal_sup_origin_mul_normal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b))
    (hsep : mixedExterior (internalSubspace b) ⊓ I = pureExterior (internalSubspace b))
    (c : Fin 2 → E) (hc₀ : c 0 ∈ internalSubspace b)
    (hc₁ : c 1 ∈ internalSubspace b) (hpair : LinearIndependent k ![c 0, c 1]) :
    IsotropicChart.normalIdeal k μ ν ≤ centeredRelationIdeal I b c ⊔
      IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν := by
  rw [IsotropicChart.normalIdeal, Ideal.span_le]
  rintro _ ⟨⟨r, j⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ := exists_cup_dual_centeredLinearPolynomial_eq_split_normal_X
    I b hsep c hc₀ hc₁ hpair r j
  have hp : centeredRelationPolynomial I b c ρ ∈ centeredRelationIdeal I b c :=
    Ideal.subset_span (Set.mem_range_self ρ)
  rw [centeredRelationPolynomial_of_center_relation_zero I b c ρ
    (split_relation_zero_of_internal I b hiso _ _ hc₀ hc₁), hρ] at hp
  have hp' := (le_sup_left : centeredRelationIdeal I b c ≤ centeredRelationIdeal I b c ⊔
    IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν) hp
  have hq := (le_sup_right :
      IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν ≤
      centeredRelationIdeal I b c ⊔
        IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν)
    (fullQuadratic_mem_origin_mul_normal I b hiso ρ)
  simpa only [add_sub_cancel_right] using
    (centeredRelationIdeal I b c ⊔
      IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν).sub_mem hp' hq

/-- Actual Nakayama yields equality of the actual complete frame and
normal ideals at the genuine origin. The required finite generation and
both ideal containments have been proved from the original objects. -/
theorem localized_centeredRelationIdeal_eq_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b))
    (hsep : mixedExterior (internalSubspace b) ⊓ I = pureExterior (internalSubspace b))
    (c : Fin 2 → E) (hc₀ : c 0 ∈ internalSubspace b)
    (hc₁ : c 1 ∈ internalSubspace b) (hpair : LinearIndependent k ![c 0, c 1]) :
    Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν))
      (Localization.AtPrime (IsotropicChart.originIdeal k (μ ⊕ ν))))
      (centeredRelationIdeal I b c) =
    Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν))
      (Localization.AtPrime (IsotropicChart.originIdeal k (μ ⊕ ν))))
      (IsotropicChart.normalIdeal k μ ν) := by
  let R := CoordinateRing k (μ ⊕ ν)
  let m : Ideal R := IsotropicChart.originIdeal k (μ ⊕ ν)
  let A := Localization.AtPrime m
  let f : R →+* A := algebraMap R A
  have hforward : Ideal.map f (centeredRelationIdeal I b c) ≤
      Ideal.map f (IsotropicChart.normalIdeal k μ ν) :=
    Ideal.map_mono (centeredRelationIdeal_le_normalIdeal I b hiso c hc₀ hc₁)
  have hmod : Ideal.map f (IsotropicChart.normalIdeal k μ ν) ≤
      Ideal.map f (centeredRelationIdeal I b c ⊔
        IsotropicChart.originIdeal k (μ ⊕ ν) * IsotropicChart.normalIdeal k μ ν) :=
    Ideal.map_mono (normalIdeal_le_centeredRelationIdeal_sup_origin_mul_normal
      I b hiso hsep c hc₀ hc₁ hpair)
  rw [Ideal.map_sup, Ideal.map_mul] at hmod
  have hm : Ideal.map f (IsotropicChart.originIdeal k (μ ⊕ ν)) = IsLocalRing.maximalIdeal A :=
    Localization.AtPrime.map_eq_maximalIdeal
  rw [hm] at hmod
  have hfg : (Ideal.map f (IsotropicChart.normalIdeal k μ ν)).FG :=
    (IsotropicChart.normalIdeal_fg (k := k) (μ := μ) (ν := ν)).map f
  apply le_antisymm hforward
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  simpa only [Ideal.smul_eq_mul] using hmod

/-- There is an actual scalar nonzero at the origin clearing every
normal equation into the actual complete frame equation ideal. -/
theorem exists_denominator_normal_mem_centeredRelationIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b))
    (hsep : mixedExterior (internalSubspace b) ⊓ I = pureExterior (internalSubspace b))
    (c : Fin 2 → E) (hc₀ : c 0 ∈ internalSubspace b)
    (hc₁ : c 1 ∈ internalSubspace b) (hpair : LinearIndependent k ![c 0, c 1]) :
    ∃ s : CoordinateRing k (μ ⊕ ν), s ∉ IsotropicChart.originIdeal k (μ ⊕ ν) ∧
      ∀ x ∈ IsotropicChart.normalIdeal k μ ν, s * x ∈ centeredRelationIdeal I b c :=
  exists_denominator_mul_mem_of_localized_ideal_le
    (centeredRelationIdeal I b c) (IsotropicChart.normalIdeal k μ ν)
    (IsotropicChart.originIdeal k (μ ⊕ ν))
    IsotropicChart.normalIdeal_fg
    (le_of_eq (localized_centeredRelationIdeal_eq_normalIdeal
      I b hiso hsep c hc₀ hc₁ hpair).symm)

/-- The true complete frame and normal ideals agree after inversion of
one actually constructed scalar outside the actual origin ideal. -/
theorem exists_principal_neighborhood_centeredRelationIdeal_eq_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (μ ⊕ ν) k E)
    (hiso : IsCupIsotropic I (internalSubspace b))
    (hsep : mixedExterior (internalSubspace b) ⊓ I = pureExterior (internalSubspace b))
    (c : Fin 2 → E) (hc₀ : c 0 ∈ internalSubspace b)
    (hc₁ : c 1 ∈ internalSubspace b) (hpair : LinearIndependent k ![c 0, c 1]) :
    ∃ s : CoordinateRing k (μ ⊕ ν), s ∉ IsotropicChart.originIdeal k (μ ⊕ ν) ∧
      Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν)) (Localization.Away s))
        (centeredRelationIdeal I b c) =
      Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν)) (Localization.Away s))
        (IsotropicChart.normalIdeal k μ ν) :=
  exists_away_ideal_equality_of_prime_localized_equality
    (centeredRelationIdeal I b c) (IsotropicChart.normalIdeal k μ ν)
    (IsotropicChart.originIdeal k (μ ⊕ ν)) IsotropicChart.normalIdeal_fg
    (centeredRelationIdeal_le_normalIdeal I b hiso c hc₀ hc₁)
    (localized_centeredRelationIdeal_eq_normalIdeal I b hiso hsep c hc₀ hc₁ hpair)

end InfiniteField

end ChenRanks.Resonance.IsotropicFrame
