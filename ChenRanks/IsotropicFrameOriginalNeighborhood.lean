import ChenRanks.IsotropicFrameLocalIdeal
import ChenRanks.IsotropicPairAdaptedBasis

/-!
# Principal neighborhoods in fixed frame coordinates

Basis extension constructs a finite adapted basis for each independent
pair. A polynomial algebra equivalence transports the centered equations
and their denominator to fixed frame coordinates. On the resulting
principal neighborhood, every coordinate solution has both rows in the
given isotropic subspace.

The statements concern coordinate solutions for the quotient cup map.
-/

noncomputable section

namespace ChenRanks.Resonance.IsotropicFrame

universe u v

variable {k : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]

section SplitBasis

variable {μ ν : Type u} [Fintype μ] [Fintype ν]

/-- The genuine internal span is characterized by vanishing of all actual
normal basis coordinates; the reverse direction uses true basis reconstruction. -/
theorem mem_internalSubspace_iff_normal_coordinates_zero
    (b : _root_.Module.Basis (μ ⊕ ν) k E) (x : E) :
    x ∈ internalSubspace b ↔ ∀ j : ν, b.repr x (Sum.inr j) = 0 := by
  constructor
  · intro hx j
    exact (Submodule.mem_dualAnnihilator (W := internalSubspace b)
      (splitNormalCoordinate b j)).mp
        (splitNormalCoordinate_mem_dualAnnihilator b j) x hx
  · intro hx
    classical
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    rcases i with i | j
    · exact (internalSubspace b).smul_mem _ (internalBasis_mem_internalSubspace b i)
    · rw [hx j, zero_smul]
      exact (internalSubspace b).zero_mem

end SplitBasis

section FiniteDimensional

variable [FiniteDimensional k E]

/-- A true finite split full basis is constructed from the original
subspace and independent pair. Its full internal span equals that P. -/
theorem exists_finite_split_basis_of_independent_pair
    (P : Submodule k E) (a₀ a₁ : E) (ha₀ : a₀ ∈ P) (ha₁ : a₁ ∈ P)
    (hpair : LinearIndependent k ![a₀, a₁]) :
    ∃ m n : ℕ, ∃ b : _root_.Module.Basis
        ((Fin 2 ⊕ ULift.{u} (Fin m)) ⊕ ULift.{u} (Fin n)) k E,
      b (Sum.inl (Sum.inl 0)) = a₀ ∧ b (Sum.inl (Sum.inl 1)) = a₁ ∧
        internalSubspace b = P := by
  obtain ⟨m, n, b₀, h₀, h₁, hP⟩ :=
    IsotropicChart.exists_finite_adapted_basis_of_independent_pair P a₀ a₁ ha₀ ha₁ hpair
  let e := Equiv.sumAssoc (Fin 2) (ULift.{u} (Fin m)) (ULift.{u} (Fin n))
  let b := b₀.reindex e.symm
  have hhead (r : Fin 2) : b (Sum.inl (Sum.inl r)) = b₀ (Sum.inl r) := by
    simp [b, e, _root_.Module.Basis.reindex_apply]
  have hinternal (i : ULift.{u} (Fin m)) :
      b (Sum.inl (Sum.inr i)) = b₀ (Sum.inr (Sum.inl i)) := by
    simp [b, e, _root_.Module.Basis.reindex_apply]
  have himage : b '' Set.range
      (Sum.inl : (Fin 2 ⊕ ULift.{u} (Fin m)) →
        (Fin 2 ⊕ ULift.{u} (Fin m)) ⊕ ULift.{u} (Fin n)) =
      b₀ '' (IsotropicChart.internalIndices : Set
        (Fin 2 ⊕ (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)))) := by
    ext z
    constructor
    · rintro ⟨i, ⟨j, rfl⟩, rfl⟩
      rcases j with r | j
      · exact ⟨Sum.inl r, by simp [IsotropicChart.internalIndices], (hhead r).symm⟩
      · exact ⟨Sum.inr (Sum.inl j), by simp [IsotropicChart.internalIndices],
          (hinternal j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      rcases i with r | j
      · exact ⟨Sum.inl (Sum.inl r), ⟨Sum.inl r, rfl⟩, hhead r⟩
      · rcases j with j | j
        · exact ⟨Sum.inl (Sum.inr j), ⟨Sum.inr j, rfl⟩, hinternal j⟩
        · exact False.elim (hi j rfl)
  refine ⟨m, n, b, (hhead 0).trans h₀, (hhead 1).trans h₁, ?_⟩
  change Submodule.span k (b '' Set.range _) = P
  rw [himage]
  exact hP

end FiniteDimensional

section OriginalCoordinates

variable {σ : Type u} [Fintype σ] [Infinite k]

/-- Every actual independent original frame inside a separated isotropic P
has a constructed principal neighborhood in the original fixed coordinates.
Every actual original-cup solution in it has both original rows in P. -/
theorem exists_original_principal_neighborhood_rows_mem
    (I : Submodule k (⋀[k]^2 E)) (b₀ : _root_.Module.Basis σ k E)
    (P : Submodule k E) (hiso : IsCupIsotropic I P)
    (hsep : mixedExterior P ⊓ I = pureExterior P)
    (x₀ : Fin 2 × σ → k) (hx₀ : row b₀ x₀ 0 ∈ P) (hx₁ : row b₀ x₀ 1 ∈ P)
    (hpair : LinearIndependent k ![row b₀ x₀ 0, row b₀ x₀ 1]) :
    ∃ t : CoordinateRing k σ, MvPolynomial.aeval x₀ t ≠ 0 ∧
      ∀ x : Fin 2 × σ → k,
        relationIdeal I b₀ ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom →
        MvPolynomial.aeval x t ≠ 0 → row b₀ x 0 ∈ P ∧ row b₀ x 1 ∈ P := by
  letI : FiniteDimensional k E := b₀.finiteDimensional_of_finite
  obtain ⟨m, n, b, _h₀, _h₁, hP⟩ := exists_finite_split_basis_of_independent_pair
    P (row b₀ x₀ 0) (row b₀ x₀ 1) hx₀ hx₁ hpair
  let c : Fin 2 → E := fun r ↦ row b₀ x₀ r
  have hiso' : IsCupIsotropic I (internalSubspace b) := by
    rw [hP]
    exact hiso
  have hsep' : mixedExterior (internalSubspace b) ⊓ I = pureExterior (internalSubspace b) :=
    by rw [hP]; exact hsep
  have hc₀ : c 0 ∈ internalSubspace b := by rw [hP]; exact hx₀
  have hc₁ : c 1 ∈ internalSubspace b := by rw [hP]; exact hx₁
  obtain ⟨s, hs, hclear⟩ := exists_denominator_normal_mem_centeredRelationIdeal
    I b hiso' hsep' c hc₀ hc₁ hpair
  let t := (coordinateChangeAlgEquiv b₀ b c).symm s
  have hxcenter : centerCoordinates b₀ c = x₀ := by
    funext q
    change b₀.repr (row b₀ x₀ q.1) q.2 = x₀ q
    exact repr_row b₀ x₀ q.1 q.2
  have hs₀ : MvPolynomial.aeval (0 : Fin 2 ×
      ((Fin 2 ⊕ ULift.{u} (Fin m)) ⊕ ULift.{u} (Fin n)) → k) s ≠ 0 := hs
  refine ⟨t, ?_, ?_⟩
  · change MvPolynomial.aeval x₀ ((coordinateChangeAlgEquiv b₀ b c).symm s) ≠ 0
    rw [← hxcenter, aeval_coordinateChangeAlgEquiv_symm_at_center]
    exact hs₀
  · intro x hxI hxt
    let y := centeredCoordinates b₀ b c x
    have hsy : MvPolynomial.aeval y s ≠ 0 := by
      change MvPolynomial.aeval (centeredCoordinates b₀ b c x) s ≠ 0
      rw [← aeval_coordinateChangeAlgEquiv_symm]
      exact hxt
    have hrow (r : Fin 2) : c r + row b y r = row b₀ x r := by
      change c r + row b (centeredCoordinates b₀ b c x) r = row b₀ x r
      rw [row_centeredCoordinates]
      abel
    have hyI : centeredRelationIdeal I b c ≤
        RingHom.ker (MvPolynomial.aeval y).toRingHom := by
      apply (centeredRelationIdeal_le_ker_aeval_iff I b c y).mpr
      rw [hrow 0, hrow 1]
      exact (relationIdeal_le_ker_aeval_iff I b₀ x).mp hxI
    have hnormal (r : Fin 2) (j : ULift.{u} (Fin n)) : y (r, Sum.inr j) = 0 := by
      have h := hyI (hclear (MvPolynomial.X (r, Sum.inr j))
        (IsotropicChart.normal_X_mem_normalIdeal r j))
      change MvPolynomial.aeval y (s * MvPolynomial.X (r, Sum.inr j)) = 0 at h
      rw [map_mul, MvPolynomial.aeval_X] at h
      exact (mul_eq_zero.mp h).resolve_left hsy
    have hmem (r : Fin 2) : row b y r ∈ internalSubspace b := by
      apply (mem_internalSubspace_iff_normal_coordinates_zero b (row b y r)).mpr
      intro j
      rw [repr_row]
      exact hnormal r j
    have hfirst : row b₀ x 0 ∈ internalSubspace b := by
      rw [← hrow 0]
      exact (internalSubspace b).add_mem hc₀ (hmem 0)
    have hsecond : row b₀ x 1 ∈ internalSubspace b := by
      rw [← hrow 1]
      exact (internalSubspace b).add_mem hc₁ (hmem 1)
    exact ⟨hP ▸ hfirst, hP ▸ hsecond⟩

end OriginalCoordinates

end ChenRanks.Resonance.IsotropicFrame
