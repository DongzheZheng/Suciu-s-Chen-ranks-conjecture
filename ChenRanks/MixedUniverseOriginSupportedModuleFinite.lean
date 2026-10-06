import ChenRanks.FiniteModuleVanishingDenominator
import ChenRanks.MixedUniverseSymmetricDualOriginPowerFinite
import ChenRanks.AnnihilatorQuotientFiniteModule
import ChenRanks.KoszulLocalizedTransverse
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Base-field finiteness from genuine nonzero-point vanishing

The coefficient ring, ideals, evaluation primes and module are the
original objects, with independent universes for the base, vector space
and module. A genuine finite module has a common annihilating denominator
at each vanishing localization. True nonzero evaluation specialization
of every punctured prime therefore forces the actual origin into the
actual annihilator radical. Genuine Noetherianity supplies a power,
and the actual annihilator quotient/tensor equivalence then proves the
same original module finite over the base. No support, radical, power,
or base-field-finiteness conclusion is input.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k] [IsAlgClosed k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (M : Type*) [AddCommGroup M]
  [_root_.Module (S k (_root_.Module.Dual k E)) M]
  [_root_.Module.Finite (S k (_root_.Module.Dual k E)) M]

theorem mixedUniverseOriginIdeal_le_annihilator_radical
    (hzero : ∀ (e : E), e ≠ 0 →
      Subsingleton
        (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
          ⊗[S k (_root_.Module.Dual k E)] M)) :
    mixedUniverseSymmetricDualOriginIdeal k E ≤
      (_root_.Module.annihilator (S k (_root_.Module.Dual k E)) M).radical := by
  classical
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro p hp
  by_contra hnot
  let q : PrimeSpectrum (S k (_root_.Module.Dual k E)) := ⟨p, hp.2⟩
  have hq : q ∈ mixedUniverseSymmetricDualPuncturedOpen k E := by
    change ¬ mixedUniverseSymmetricDualOriginIdeal k E ≤ p
    exact hnot
  obtain ⟨e, he, hpe⟩ :=
    mixedUniverse_symmetricDual_puncturedPrime_exists_nonzero_evaluation_specialization
      k E q hq
  letI := hzero e he
  obtain ⟨d, hd, hdann⟩ := ChenRanks.finiteModule_exists_annihilating_denominator
    (S k (_root_.Module.Dual k E))
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
    (pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e)).primeCompl M
  exact hd (hpe (hp.1 hdann))

theorem mixedUniverseOriginIdeal_exists_pow_le_annihilator
    (hzero : ∀ (e : E), e ≠ 0 →
      Subsingleton
        (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
          ⊗[S k (_root_.Module.Dual k E)] M)) :
    ∃ n : ℕ, mixedUniverseSymmetricDualOriginIdeal k E ^ n ≤
      _root_.Module.annihilator (S k (_root_.Module.Dual k E)) M := by
  letI := mixedUniverse_symmetricDual_finiteType k E
  letI : IsNoetherianRing (S k (_root_.Module.Dual k E)) :=
    Algebra.FiniteType.isNoetherianRing k (S k (_root_.Module.Dual k E))
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    (mixedUniverseOriginIdeal_le_annihilator_radical k E M hzero)
    (IsNoetherian.noetherian (mixedUniverseSymmetricDualOriginIdeal k E))

/-- The actual finite original module becomes finite over the base field
by the preceding true annihilator-power and quotient/tensor arguments. -/
theorem mixedUniverseOriginSupportedModule_finite_over_base
    [_root_.Module k M] [IsScalarTower k (S k (_root_.Module.Dual k E)) M]
    (hzero : ∀ (e : E), e ≠ 0 →
      Subsingleton
        (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
          ⊗[S k (_root_.Module.Dual k E)] M)) :
    _root_.Module.Finite k M := by
  obtain ⟨n, hn⟩ := mixedUniverseOriginIdeal_exists_pow_le_annihilator k E M hzero
  letI : _root_.Module.Finite k
      ((S k (_root_.Module.Dual k E)) ⧸
        _root_.Module.annihilator (S k (_root_.Module.Dual k E)) M) :=
    mixedUniverseOriginPowerQuotient_finite k E
      (_root_.Module.annihilator (S k (_root_.Module.Dual k E)) M) n hn
  exact ChenRanks.finiteModule_of_annihilatorQuotient_finite k
    (S k (_root_.Module.Dual k E)) M

end ChenRanks.Koszul
