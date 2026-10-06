import ChenRanks.IsotropicFrameRelationCoordinateChange
import ChenRanks.IsotropicAdaptedGraphCoordinates

/-!
# The complete frame derivative and normal coordinates

The derivative acts on two vectors of the full ambient space. Separation
and independence of the center pair determine its kernel. Dual-map
factorization constructs the cup-target functionals that yield the normal
coordinate forms in an adapted basis.

All frame directions are retained, including the four directions that
change the ordered basis within its two-dimensional span.
-/

noncomputable section

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]

/-- Actual evaluation of one of the two complete frame directions. -/
def frameProjection (r : Fin 2) : (Fin 2 → E) →ₗ[k] E where
  toFun a := a r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem frameProjection_apply (r : Fin 2) (a : Fin 2 → E) :
    frameProjection (k := k) r a = a r := rfl

/-- Actual exterior separation forces both complete directions in the
true derivative kernel into the original subspace. -/
theorem directions_mem_of_centeredDifferential_eq_zero
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hsep : mixedExterior P ⊓ I = pureExterior P)
    (c : Fin 2 → E) (hc₀ : c 0 ∈ P) (hc₁ : c 1 ∈ P)
    (hpair : LinearIndependent k ![c 0, c 1])
    (a : Fin 2 → E) (ha : centeredDifferential I c a = 0) :
    a 0 ∈ P ∧ a 1 ∈ P := by
  have hrel : exteriorWedge (k := k) (a 0) (c 1) +
      exteriorWedge (c 0) (a 1) ∈ I := by
    apply (cupQuotient_eq_zero_iff I _).mp
    simpa only [centeredDifferential_apply, relationWedge_apply, map_add] using ha
  exact tangent_representatives_mem_of_separated_relation I P hsep
    (c 0) (c 1) (a 0) (a 1) hc₀ hc₁ hpair hrel

/-- Genuine original isotropy makes the complete derivative vanish on
two actual directions lying in the original subspace. -/
theorem centeredDifferential_eq_zero_of_directions_mem
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hiso : IsCupIsotropic I P) (c : Fin 2 → E)
    (hc₀ : c 0 ∈ P) (hc₁ : c 1 ∈ P)
    (a : Fin 2 → E) (ha₀ : a 0 ∈ P) (ha₁ : a 1 ∈ P) :
    centeredDifferential I c a = 0 := by
  have h₀ := (isCupIsotropic_iff_isIsotropic I P).mp hiso
    (a 0) ha₀ (c 1) hc₁
  have h₁ := (isCupIsotropic_iff_isIsotropic I P).mp hiso
    (c 0) hc₀ (a 1) ha₁
  simp only [centeredDifferential_apply, h₀, h₁, add_zero]

/-- The exact complete derivative kernel is proved from actual original
isotropy, separation, and independence of the center pair. -/
theorem mem_ker_centeredDifferential_iff_directions_mem
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hiso : IsCupIsotropic I P) (hsep : mixedExterior P ⊓ I = pureExterior P)
    (c : Fin 2 → E) (hc₀ : c 0 ∈ P) (hc₁ : c 1 ∈ P)
    (hpair : LinearIndependent k ![c 0, c 1]) (a : Fin 2 → E) :
    a ∈ LinearMap.ker (centeredDifferential I c) ↔ a 0 ∈ P ∧ a 1 ∈ P := by
  constructor
  · intro ha
    exact directions_mem_of_centeredDifferential_eq_zero I P hsep c
      hc₀ hc₁ hpair a ha
  · rintro ⟨ha₀, ha₁⟩
    exact centeredDifferential_eq_zero_of_directions_mem I P hiso c
      hc₀ hc₁ a ha₀ ha₁

/-- Each actual linear form annihilating the original P, on either
complete direction, is the dual of the true derivative. The cup-target
dual is constructed through the actual dual-map range theorem. -/
theorem exists_cup_dual_for_centered_annihilating_direction
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hsep : mixedExterior P ⊓ I = pureExterior P)
    (c : Fin 2 → E) (hc₀ : c 0 ∈ P) (hc₁ : c 1 ∈ P)
    (hpair : LinearIndependent k ![c 0, c 1])
    (ℓ : E →ₗ[k] k) (hℓ : ℓ ∈ P.dualAnnihilator) (r : Fin 2) :
    ∃ ρ : CupTarget I →ₗ[k] k, ∀ a : Fin 2 → E,
      ρ (centeredDifferential I c a) = ℓ (a r) := by
  have hvanish : ℓ.comp (frameProjection r) ∈
      (LinearMap.ker (centeredDifferential I c)).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro a ha
    have hmem := directions_mem_of_centeredDifferential_eq_zero I P hsep c
      hc₀ hc₁ hpair a ha
    apply (Submodule.mem_dualAnnihilator (W := P) ℓ).mp hℓ
    fin_cases r
    · exact hmem.1
    · exact hmem.2
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hvanish
  obtain ⟨ρ, hρ⟩ := hvanish
  refine ⟨ρ, ?_⟩
  intro a
  have h := DFunLike.congr_fun hρ a
  simpa only [LinearMap.comp_apply, frameProjection_apply] using h

section FiniteCoordinates

variable {τ : Type u} [Fintype τ] [Infinite k]

/-- A constructed actual derivative factorization by a basis coordinate
identifies the actual complete linear polynomial with that literal X. -/
theorem centeredLinearPolynomial_eq_X_of_coordinate_factor
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis τ k E)
    (c : Fin 2 → E) (ρ : CupTarget I →ₗ[k] k) (r : Fin 2) (j : τ)
    (hρ : ∀ a : Fin 2 → E,
      ρ (centeredDifferential I c a) = b.coord j (a r)) :
    centeredLinearPolynomial I b c ρ = MvPolynomial.X (r, j) := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x (centeredLinearPolynomial I b c ρ) =
    MvPolynomial.aeval x (MvPolynomial.X (r, j))
  rw [aeval_centeredLinearPolynomial, MvPolynomial.aeval_X, hρ]
  change b.repr (row b x r) j = x (r, j)
  exact repr_row b x r j

/-- For any actual basis coordinate annihilating P, the original cup
equations genuinely supply its literal normal variable on either row. -/
theorem exists_cup_dual_centeredLinearPolynomial_eq_normal_X
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hsep : mixedExterior P ⊓ I = pureExterior P)
    (b : _root_.Module.Basis τ k E) (c : Fin 2 → E)
    (hc₀ : c 0 ∈ P) (hc₁ : c 1 ∈ P)
    (hpair : LinearIndependent k ![c 0, c 1]) (r : Fin 2) (j : τ)
    (hj : b.coord j ∈ P.dualAnnihilator) :
    ∃ ρ : CupTarget I →ₗ[k] k,
      centeredLinearPolynomial I b c ρ = MvPolynomial.X (r, j) := by
  obtain ⟨ρ, hρ⟩ := exists_cup_dual_for_centered_annihilating_direction
    I P hsep c hc₀ hc₁ hpair (b.coord j) hj r
  exact ⟨ρ, centeredLinearPolynomial_eq_X_of_coordinate_factor I b c ρ r j hρ⟩

end FiniteCoordinates

section AdaptedBasis

variable {μ ν : Type u} [Fintype μ] [Fintype ν] [Infinite k]

omit [Fintype μ] [Fintype ν] [Infinite k] in
private theorem adaptedCenterPair_independent
    (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E) :
    LinearIndependent k ![b (Sum.inl 0), b (Sum.inl 1)] := by
  have hfun : ![b (Sum.inl 0), b (Sum.inl 1)] =
      (fun r : Fin 2 ↦ b (Sum.inl r)) := by
    funext r
    fin_cases r <;> rfl
  rw [hfun]
  exact b.linearIndependent.comp (Sum.inl : Fin 2 → Fin 2 ⊕ (μ ⊕ ν))
    Sum.inl_injective

/-- Actual adapted-basis normal coordinates satisfy the required
annihilator condition by the already proved basis-support theorem.
All complete frame variables, including the two distinguished columns,
remain in the true polynomial ring in this conclusion. -/
theorem exists_cup_dual_centeredLinearPolynomial_eq_adapted_normal_X
    (I : Submodule k (⋀[k]^2 E))
    (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hsep : mixedExterior (IsotropicChart.adaptedSubspace b) ⊓ I =
      pureExterior (IsotropicChart.adaptedSubspace b)) (r : Fin 2) (j : ν) :
    ∃ ρ : CupTarget I →ₗ[k] k,
      centeredLinearPolynomial I b (fun s ↦ b (Sum.inl s)) ρ =
        MvPolynomial.X (r, Sum.inr (Sum.inr j)) := by
  exact exists_cup_dual_centeredLinearPolynomial_eq_normal_X
    I (IsotropicChart.adaptedSubspace b) hsep b (fun s ↦ b (Sum.inl s))
    (IsotropicChart.distinguished_mem_adaptedSubspace b 0)
    (IsotropicChart.distinguished_mem_adaptedSubspace b 1)
    (adaptedCenterPair_independent b) r (Sum.inr (Sum.inr j))
    (IsotropicChart.normalCoordinate_mem_dualAnnihilator b j)

end AdaptedBasis

end ChenRanks.Resonance.IsotropicFrame
