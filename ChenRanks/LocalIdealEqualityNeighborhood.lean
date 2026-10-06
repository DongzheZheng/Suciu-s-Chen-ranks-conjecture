import ChenRanks.IsotropicChartPolynomialDecomposition
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Actual finite-denominator neighborhoods of localized ideal equality

A genuine finitely generated ideal containment after prime localization
has one actual denominator outside that prime clearing all its generators.
Actual localization away from this denominator gives the corresponding
ideal containment. Combining it with the opposite original containment
produces equality on a genuine principal open neighborhood.

The original graph-chart application supplies finite generation and both
containments from the already proved original isotropy, separation and
Nakayama theorem. Global component finiteness is not an input or conclusion.
-/

noncomputable section

namespace ChenRanks

variable {R : Type*} [CommRing R]

/-- A genuine finite set of generators admits one actual denominator
    outside the original prime, clearing every element of the ideal. -/
theorem exists_denominator_mul_mem_of_localized_ideal_le
    (I J p : Ideal R) [p.IsPrime] (hfg : J.FG)
    (hle : J.map (algebraMap R (Localization.AtPrime p)) ≤
      I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ ∀ x ∈ J, s * x ∈ I := by
  classical
  obtain ⟨G, hG⟩ := hfg
  have hgenerator (i : G) : ∃ d : R, d ∈ p.primeCompl ∧ d * (i : R) ∈ I := by
    have hi : (i : R) ∈ J := hG ▸ Submodule.subset_span i.property
    have himap := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) hi
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) I (i : R)).mp (hle himap)
  choose d hd hdI using hgenerator
  let D (i : G) : p.primeCompl := ⟨d i, hd i⟩
  let s : p.primeCompl := ∏ i : G, D i
  have hsprod : (s : R) = ∏ i : G, d i := by simp [s, D]
  have hclear (i : G) : (s : R) * (i : R) ∈ I := by
    have hdiv : d i ∣ (s : R) := by
      rw [hsprod]
      exact Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    obtain ⟨c, hc⟩ := hdiv
    rw [hc]
    convert I.mul_mem_left c (hdI i) using 1; ring
  let muls : R →ₗ[R] R :=
    { toFun := fun x ↦ (s : R) * x
      map_add' := fun x y ↦ mul_add (s : R) x y
      map_smul' := by
        intro c x
        simp only [smul_eq_mul, RingHom.id_apply]
        exact mul_left_comm (s : R) c x }
  have hsub : J ≤ Submodule.comap muls I := by
    rw [← hG]
    apply Submodule.span_le.mpr
    intro x hx
    change (s : R) * x ∈ I
    exact hclear ⟨x, hx⟩
  exact ⟨s, s.property, fun x hx ↦ hsub hx⟩

/-- Actual equality on prime localization descends to actual equality
    after inverting one genuine scalar outside the original prime. -/
theorem exists_away_ideal_equality_of_prime_localized_equality
    (I J p : Ideal R) [p.IsPrime] (hfg : J.FG) (hIJ : I ≤ J)
    (hlocal : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨s, hs, hclear⟩ := exists_denominator_mul_mem_of_localized_ideal_le I J p
    hfg (le_of_eq hlocal.symm)
  refine ⟨s, hs, le_antisymm (Ideal.map_mono hIJ) ?_⟩
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change algebraMap R (Localization.Away s) x ∈ I.map (algebraMap R (Localization.Away s))
  have hmul := Ideal.mem_map_of_mem (algebraMap R (Localization.Away s)) (hclear x hx)
  rw [map_mul] at hmul
  exact (Ideal.unit_mul_mem_iff_mem _
    (IsLocalization.Away.algebraMap_isUnit s)).mp hmul

end ChenRanks

namespace ChenRanks.Resonance.IsotropicChart

universe u v

variable {k μ ν : Type u} {E : Type v} [Field k] [AddCommGroup E] [Module k E]
  [Fintype μ] [Fintype ν]

/-- The genuine original graph equations and normal coordinate equations
    agree after inversion of an actually constructed scalar nonzero at
    the actual origin. All ideal hypotheses are supplied by the proved
    original isotropy and exterior separation. -/
theorem exists_principal_neighborhood_relationIdeal_eq_normalIdeal
    (I : Submodule k (⋀[k]^2 E)) (b : _root_.Module.Basis (Fin 2 ⊕ (μ ⊕ ν)) k E)
    (hiso : IsCupIsotropic I (adaptedSubspace b))
    (hsep : mixedExterior (adaptedSubspace b) ⊓ I = pureExterior (adaptedSubspace b)) :
    ∃ s : CoordinateRing k (μ ⊕ ν), s ∉ originIdeal k (μ ⊕ ν) ∧
      Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν)) (Localization.Away s)) (relationIdeal I b) =
      Ideal.map (algebraMap (CoordinateRing k (μ ⊕ ν)) (Localization.Away s)) (normalIdeal k μ ν) :=
  exists_away_ideal_equality_of_prime_localized_equality
    (relationIdeal I b) (normalIdeal k μ ν) (originIdeal k (μ ⊕ ν))
    normalIdeal_fg (relationIdeal_le_normalIdeal_of_adapted_isotropic I b hiso)
    (localized_relationIdeal_eq_normalIdeal I b hiso hsep)

end ChenRanks.Resonance.IsotropicChart
