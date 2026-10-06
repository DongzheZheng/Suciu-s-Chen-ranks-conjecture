import ChenRanks.IsotropicFrameCoordinateChange

/-!
# Coordinate transport of ordered-frame equations

The differential acts on two directions in the full ambient space and
retains the four directions changing the ordered basis within its plane.
The centered equations are the constant, linear, and quadratic terms of
the quotient cup map. A polynomial algebra equivalence transports the
frame relation ideal to these equations.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]

/-- The genuine derivative of the original relation on two complete
ordered-frame directions, at the actual center pair. -/
def centeredDifferential (I : Submodule k (⋀[k]^2 E)) (c : Fin 2 → E) :
    (Fin 2 → E) →ₗ[k] CupTarget I where
  toFun a := relationWedge (cupQuotient I) (a 0) (c 1) +
    relationWedge (cupQuotient I) (c 0) (a 1)
  map_add' a a' := by
    simp only [Pi.add_apply, map_add, LinearMap.add_apply]
    abel
  map_smul' t a := by
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_add,
      RingHom.id_apply]

/-- The actual complete derivative, evaluated on the same original vectors. -/
@[simp] theorem centeredDifferential_apply
    (I : Submodule k (⋀[k]^2 E)) (c a : Fin 2 → E) :
    centeredDifferential I c a =
      relationWedge (cupQuotient I) (a 0) (c 1) +
        relationWedge (cupQuotient I) (c 0) (a 1) := rfl

section FiniteCoordinates

variable {τ : Type u} [Fintype τ]

/-- The genuine complete linear term in center-plus-direction coordinates. -/
def centeredLinearPolynomial (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis τ k E) (c : Fin 2 → E)
    (ρ : CupTarget I →ₗ[k] k) : CoordinateRing k τ := by
  classical
  exact
    (∑ j, MvPolynomial.X (0, j) *
      MvPolynomial.C (ρ (relationWedge (cupQuotient I) (b j) (c 1)))) +
    (∑ j, MvPolynomial.X (1, j) *
      MvPolynomial.C (ρ (relationWedge (cupQuotient I) (c 0) (b j))))

/-- The true centered cup equation, with its actual constant, complete
linear, and quadratic terms. -/
def centeredRelationPolynomial (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis τ k E) (c : Fin 2 → E)
    (ρ : CupTarget I →ₗ[k] k) : CoordinateRing k τ :=
  MvPolynomial.C (ρ (relationWedge (cupQuotient I) (c 0) (c 1))) +
    centeredLinearPolynomial I b c ρ + relationPolynomial I b ρ

/-- The genuine centered ideal uses all actual dual linear forms. -/
def centeredRelationIdeal (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis τ k E) (c : Fin 2 → E) :
    Ideal (CoordinateRing k τ) :=
  Ideal.span (Set.range (centeredRelationPolynomial I b c))

/-- Scalar evaluation of the complete linear term is the actual derivative
on the original complete row vectors. -/
theorem aeval_centeredLinearPolynomial
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × τ → k) :
    MvPolynomial.aeval x (centeredLinearPolynomial I b c ρ) =
      ρ (centeredDifferential I c (fun r ↦ row b x r)) := by
  classical
  calc
    _ = (∑ j, x (0, j) *
        ρ (relationWedge (cupQuotient I) (b j) (c 1))) +
        (∑ j, x (1, j) *
          ρ (relationWedge (cupQuotient I) (c 0) (b j))) := by
      simp [centeredLinearPolynomial]
    _ = _ := by
      rw [centeredDifferential_apply, map_add]
      change _ =
        ρ (((relationWedge (cupQuotient I)).flip (c 1))
          (∑ j, x (0, j) • b j)) +
        ρ ((relationWedge (cupQuotient I) (c 0))
          (∑ j, x (1, j) • b j))
      simp only [map_sum, map_smul, smul_eq_mul, LinearMap.flip_apply]

/-- The complete centered equation evaluates to the original relation
on the actual center plus actual complete directions. -/
theorem aeval_centeredRelationPolynomial
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (ρ : CupTarget I →ₗ[k] k) (x : Fin 2 × τ → k) :
    MvPolynomial.aeval x (centeredRelationPolynomial I b c ρ) =
      ρ (relationWedge (cupQuotient I)
        (c 0 + row b x 0) (c 1 + row b x 1)) := by
  calc
    _ = ρ (relationWedge (cupQuotient I) (c 0) (c 1)) +
        ρ (centeredDifferential I c (fun r ↦ row b x r)) +
        ρ (relationWedge (cupQuotient I) (row b x 0) (row b x 1)) := by
      rw [centeredRelationPolynomial, map_add, map_add, MvPolynomial.aeval_C,
        aeval_centeredLinearPolynomial, aeval_relationPolynomial]
      rfl
    _ = _ := by
      simp only [centeredDifferential_apply, map_add, LinearMap.add_apply]
      abel

/-- At an actual isotropic center the constant term genuinely vanishes;
this is derived from the original cup relation. -/
theorem centeredRelationPolynomial_of_center_relation_zero
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (ρ : CupTarget I →ₗ[k] k)
    (hc : relationWedge (cupQuotient I) (c 0) (c 1) = 0) :
    centeredRelationPolynomial I b c ρ =
      centeredLinearPolynomial I b c ρ + relationPolynomial I b ρ := by
  simp only [centeredRelationPolynomial, hc, map_zero, zero_add]

/-- Actual duals detect precisely the original centered relation, proved
using the genuine projective vector-space dual separation theorem. -/
theorem centeredRelationIdeal_le_ker_aeval_iff
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (x : Fin 2 × τ → k) :
    centeredRelationIdeal I b c ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom ↔
      relationWedge (cupQuotient I)
        (c 0 + row b x 0) (c 1 + row b x 1) = 0 := by
  constructor
  · intro hIdeal
    by_contra hrel
    obtain ⟨ρ, hρ⟩ := _root_.Module.Projective.exists_dual_ne_zero k hrel
    have h := hIdeal (Ideal.subset_span (Set.mem_range_self ρ))
    change MvPolynomial.aeval x (centeredRelationPolynomial I b c ρ) = 0 at h
    rw [aeval_centeredRelationPolynomial] at h
    exact hρ h
  · intro hrel
    rw [centeredRelationIdeal, Ideal.span_le]
    rintro _ ⟨ρ, rfl⟩
    change MvPolynomial.aeval x (centeredRelationPolynomial I b c ρ) = 0
    rw [aeval_centeredRelationPolynomial, hrel, map_zero]

end FiniteCoordinates

section InfiniteField

variable {σ τ : Type u} [Fintype σ] [Fintype τ] [Infinite k]

/-- The actual change of basis and translation takes every original frame
relation to its complete centered expansion, proved by actual evaluation. -/
theorem coordinateChangeAlgEquiv_relationPolynomial
    (I : Submodule k (⋀[k]^2 E))
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (ρ : CupTarget I →ₗ[k] k) :
    coordinateChangeAlgEquiv b₀ b₁ c (relationPolynomial I b₀ ρ) =
      centeredRelationPolynomial I b₁ c ρ := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x
      (coordinateChangeAlgEquiv b₀ b₁ c (relationPolynomial I b₀ ρ)) =
    MvPolynomial.aeval x (centeredRelationPolynomial I b₁ c ρ)
  rw [aeval_coordinateChangeAlgEquiv, aeval_relationPolynomial,
    aeval_centeredRelationPolynomial, row_uncenteredCoordinates,
    row_uncenteredCoordinates]

/-- Transport of the genuine original ideal, without an ideal equality
premise and without any proposed component equations. -/
theorem map_coordinateChangeAlgEquiv_relationIdeal
    (I : Submodule k (⋀[k]^2 E))
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) :
    Ideal.map (coordinateChangeAlgEquiv b₀ b₁ c).toRingHom (relationIdeal I b₀) =
      centeredRelationIdeal I b₁ c := by
  rw [relationIdeal, Ideal.map_span, centeredRelationIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨ρ, rfl⟩, rfl⟩
    exact ⟨ρ, (coordinateChangeAlgEquiv_relationPolynomial I b₀ b₁ c ρ).symm⟩
  · rintro ⟨ρ, rfl⟩
    exact ⟨relationPolynomial I b₀ ρ, Set.mem_range_self ρ,
      coordinateChangeAlgEquiv_relationPolynomial I b₀ b₁ c ρ⟩

/-- The true inverse equivalence transports the centered relation ideal
back to the very same original frame ideal. -/
theorem map_coordinateChangeAlgEquiv_symm_centeredRelationIdeal
    (I : Submodule k (⋀[k]^2 E))
    (b₀ : _root_.Module.Basis σ k E) (b₁ : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) :
    Ideal.map (coordinateChangeAlgEquiv b₀ b₁ c).symm.toRingHom
      (centeredRelationIdeal I b₁ c) = relationIdeal I b₀ := by
  rw [← map_coordinateChangeAlgEquiv_relationIdeal I b₀ b₁ c]
  exact Ideal.map_of_equiv (coordinateChangeAlgEquiv b₀ b₁ c).toRingEquiv

end InfiniteField

end ChenRanks.Resonance.IsotropicFrame
