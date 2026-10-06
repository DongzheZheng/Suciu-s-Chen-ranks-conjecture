import ChenRanks.IsotropicChartPolynomialDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual finite adapted bases for an original subspace and independent pair

An independent pair in the actual original subspace P is first extended
inside P. The resulting actual P-basis, embedded into the original vector
space, is then extended to a full basis. Both extensions preserve their
original vectors. Their genuine finite indices are reindexed to small
finite types, so the result is actual chart data for the previously defined
original graph equations. The internal coordinate span is proved to equal
the given original P. No existence of an adapted basis is a premise.
-/

noncomputable section

namespace ChenRanks.Resonance.IsotropicChart

universe u v w

private theorem sumExtend_apply_inl
    {k : Type u} {E : Type v} {ι : Type w}
    [Field k] [AddCommGroup E] [Module k E]
    {f : ι → E} (hf : LinearIndependent k f) (i : ι) :
    _root_.Module.Basis.sumExtend hf (Sum.inl i) = f i := by
  classical
  simp [_root_.Module.Basis.sumExtend, _root_.Module.Basis.reindex_apply,
    _root_.Module.Basis.extend_apply_self]
  rfl

variable {k : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [FiniteDimensional k E]

/-- Every original independent pair in an actual subspace has a genuine
    finite full basis preserving the pair and with actual internal span P.
    Reindexing shrinks both complementary index types to the field's
    universe, without replacing any original vector-space object. -/
theorem exists_finite_adapted_basis_of_independent_pair
    (P : Submodule k E) (u v : E) (hu : u ∈ P) (hv : v ∈ P)
    (huv : LinearIndependent k ![u, v]) :
    ∃ m n : ℕ, ∃ b : _root_.Module.Basis
        (Fin 2 ⊕ (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n))) k E,
      b (Sum.inl 0) = u ∧ b (Sum.inl 1) = v ∧ adaptedSubspace b = P := by
  classical
  let pv : Fin 2 → P := ![⟨u, hu⟩, ⟨v, hv⟩]
  have hpv : LinearIndependent k pv := by
    apply LinearIndependent.of_comp P.subtype
    have hfun : P.subtype ∘ pv = ![u, v] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    exact huv
  let μ₀ := _root_.Module.Basis.sumExtendIndex hpv
  let bP : _root_.Module.Basis (Fin 2 ⊕ μ₀) k P := _root_.Module.Basis.sumExtend hpv
  let f : Fin 2 ⊕ μ₀ → E := P.subtype ∘ bP
  have hf : LinearIndependent k f :=
    bP.linearIndependent.map' P.subtype (LinearMap.ker_eq_bot.mpr P.injective_subtype)
  let ν₀ := _root_.Module.Basis.sumExtendIndex hf
  let bE : _root_.Module.Basis ((Fin 2 ⊕ μ₀) ⊕ ν₀) k E :=
    _root_.Module.Basis.sumExtend hf
  letI : Fintype (Fin 2 ⊕ μ₀) := FiniteDimensional.fintypeBasisIndex bP
  letI : Fintype μ₀ := Fintype.ofInjective (Sum.inr : μ₀ → Fin 2 ⊕ μ₀) Sum.inr_injective
  letI : Fintype ((Fin 2 ⊕ μ₀) ⊕ ν₀) := FiniteDimensional.fintypeBasisIndex bE
  letI : Fintype ν₀ :=
    Fintype.ofInjective (Sum.inr : ν₀ → (Fin 2 ⊕ μ₀) ⊕ ν₀) Sum.inr_injective
  let m := Fintype.card μ₀
  let n := Fintype.card ν₀
  let eμ : μ₀ ≃ ULift.{u} (Fin m) := (Fintype.equivFin μ₀).trans Equiv.ulift.symm
  let eν : ν₀ ≃ ULift.{u} (Fin n) := (Fintype.equivFin ν₀).trans Equiv.ulift.symm
  let e : ((Fin 2 ⊕ μ₀) ⊕ ν₀) ≃
      (Fin 2 ⊕ (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n))) :=
    (Equiv.sumAssoc (Fin 2) μ₀ ν₀).trans
      (Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.sumCongr eμ eν))
  let b := bE.reindex e
  have hdistinguished (r : Fin 2) : b (Sum.inl r) = (pv r : E) := by
    simp [b, e, bE, _root_.Module.Basis.reindex_apply]
    rw [sumExtend_apply_inl hf (Sum.inl r)]
    change ((_root_.Module.Basis.sumExtend hpv) (Sum.inl r) : E) = (pv r : E)
    rw [sumExtend_apply_inl hpv r]
  have hinternal (j : ULift.{u} (Fin m)) :
      b (Sum.inr (Sum.inl j)) = f (Sum.inr (eμ.symm j)) := by
    simp [b, e, bE, _root_.Module.Basis.reindex_apply]
    exact sumExtend_apply_inl hf (Sum.inr (eμ.symm j))
  have himage : b '' (internalIndices : Set
        (Fin 2 ⊕ (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)))) = Set.range f := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases i with r | j
      · refine ⟨Sum.inl r, ?_⟩
        simp [b, e, bE, _root_.Module.Basis.reindex_apply]
        exact (sumExtend_apply_inl hf (Sum.inl r)).symm
      · rcases j with j | j
        · exact ⟨Sum.inr (eμ.symm j), (hinternal j).symm⟩
        · exact False.elim (hi j rfl)
    · rintro ⟨i, rfl⟩
      rcases i with r | j
      · refine ⟨Sum.inl r, ?_, ?_⟩
        · simp [internalIndices]
        · simp [b, e, bE, _root_.Module.Basis.reindex_apply]
          exact sumExtend_apply_inl hf (Sum.inl r)
      · refine ⟨Sum.inr (Sum.inl (eμ j)), ?_, ?_⟩
        · simp [internalIndices]
        · rw [hinternal, Equiv.symm_apply_apply]
  have hmem (i : Fin 2 ⊕ μ₀) : f i ∈ P := (bP i).property
  have hcoeff : (fun i : Fin 2 ⊕ μ₀ ↦ (⟨f i, hmem i⟩ : P)) = bP := by
    funext i
    rfl
  have hspan : Submodule.span k (Set.range f) = P := by
    apply (Submodule.span_range_subtype_eq_top_iff P hmem).mp
    rw [hcoeff]
    exact bP.span_eq
  refine ⟨m, n, b, ?_, ?_, ?_⟩
  · simpa only [pv, Matrix.cons_val_zero] using hdistinguished 0
  · simpa only [pv, Matrix.cons_val_one, Matrix.cons_val_zero] using hdistinguished 1
  · change Submodule.span k (b '' internalIndices) = P
    rw [himage]
    exact hspan

/-- The proved basis construction and actual Nakayama theorem apply to
    every given original separated isotropic P and every independent
    original pair inside it. No prechosen model or adapted chart is an input. -/
theorem exists_finite_adapted_local_ideal_of_independent_pair
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hiso : IsCupIsotropic I P) (hsep : mixedExterior P ⊓ I = pureExterior P)
    (u v : E) (hu : u ∈ P) (hv : v ∈ P) (huv : LinearIndependent k ![u, v]) :
    ∃ m n : ℕ, ∃ b : _root_.Module.Basis
        (Fin 2 ⊕ (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n))) k E,
      b (Sum.inl 0) = u ∧ b (Sum.inl 1) = v ∧ adaptedSubspace b = P ∧
      Ideal.map (algebraMap (CoordinateRing k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)))
        (Localization.AtPrime (originIdeal k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)))))
        (relationIdeal I b) =
      Ideal.map (algebraMap (CoordinateRing k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)))
        (Localization.AtPrime (originIdeal k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)))))
        (normalIdeal k (ULift.{u} (Fin m)) (ULift.{u} (Fin n))) := by
  obtain ⟨m, n, b, hb₀, hb₁, hbP⟩ :=
    exists_finite_adapted_basis_of_independent_pair P u v hu hv huv
  refine ⟨m, n, b, hb₀, hb₁, hbP, ?_⟩
  apply localized_relationIdeal_eq_normalIdeal
  · simpa only [hbP] using hiso
  · simpa only [hbP] using hsep

end ChenRanks.Resonance.IsotropicChart
