import Mathlib

/-!
# An actual DVR above a DVR in a finite separable field extension

The extension ring is constructed, rather than assumed: take the integral
closure of the base DVR in the extension field, choose a maximal ideal above
the base maximal ideal by lying over, and localize at that ideal.  The
localization is realized as an actual subalgebra of the extension field.

This does not yet construct the base DVR at a transcendental rational
function, logarithmic residue maps, or the arrangement separation theorem.
-/

namespace ChenRanks

open IsLocalRing

variable (A K F : Type*) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Field F]
  [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
  [IsScalarTower A K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]

include K

/-- A finite separable extension of the fraction field of an actual DVR
contains an actual DVR whose fraction field is the extension field and
whose maximal ideal contracts to the original maximal ideal. -/
theorem exists_discreteValuationRing_above :
    ∃ O : Subalgebra A F, ∃ hO : IsDiscreteValuationRing O,
      IsFractionRing O F ∧
        (letI : IsDiscreteValuationRing O := hO
         ∀ a : A, a ∈ maximalIdeal A ↔
           algebraMap A O a ∈ maximalIdeal O) := by
  classical
  let B := integralClosure A F
  letI : IsFractionRing B F :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K F B
  letI : IsDedekindDomain B := integralClosure.isDedekindDomain A K F
  letI : FaithfulSMul A B :=
    FaithfulSMul.of_field_isFractionRing (R := A) (S := B) K F
  obtain ⟨q, hqmax, hqlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) (maximalIdeal A)
  letI : q.IsMaximal := hqmax
  letI : q.LiesOver (maximalIdeal A) := hqlies
  have hqne : q ≠ ⊥ := by
    obtain ⟨a, ha, hane⟩ :=
      (maximalIdeal A).ne_bot_iff.mp (IsDiscreteValuationRing.not_a_field A)
    have haq : algebraMap A B a ∈ q :=
      (Ideal.mem_of_liesOver q (maximalIdeal A) a).mp ha
    intro hq
    have hzero : algebraMap A B a = 0 := by simpa [hq] using haq
    apply hane
    exact (FaithfulSMul.algebraMap_injective A B) (by simpa using hzero)
  let S : Subalgebra B F :=
    Localization.subalgebra F q.primeCompl q.primeCompl_le_nonZeroDivisors
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hqne S
  refine ⟨S.restrictScalars A, ?_, ?_, ?_⟩
  · change IsDiscreteValuationRing S
    infer_instance
  · change IsFractionRing S F
    infer_instance
  change ∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A S a ∈ maximalIdeal S
  intro a
  rw [IsScalarTower.algebraMap_apply A B S]
  exact (Ideal.mem_of_liesOver q (maximalIdeal A) a).trans
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S q (algebraMap A B a)).symm

/-- Every given nonzero element of the base maximal ideal has an actual
nonzero image in the maximal ideal of the constructed extension DVR.
In particular this applies to an actual uniformizer of the base DVR. -/
theorem exists_discreteValuationRing_above_nonzero
    (a : A) (ha : a ∈ maximalIdeal A) (hane : a ≠ 0) :
    ∃ O : Subalgebra A F, ∃ hO : IsDiscreteValuationRing O,
      IsFractionRing O F ∧
        (letI : IsDiscreteValuationRing O := hO
         algebraMap A O a ∈ maximalIdeal O ∧ algebraMap A O a ≠ 0) := by
  obtain ⟨O, hO, hfrac, hmem⟩ := exists_discreteValuationRing_above A K F
  letI : IsDiscreteValuationRing O := hO
  refine ⟨O, hO, hfrac, (hmem a).mp ha, ?_⟩
  intro hz
  have hAF : Function.Injective (algebraMap A F) :=
    algebraMap_injective_of_field_isFractionRing (R := A) (S := F) K F
  apply hane
  apply hAF
  simpa only [IsScalarTower.algebraMap_apply A O F, map_zero] using
    congrArg (algebraMap O F) hz

/-- The actual extension DVR produces a normalized discrete field
valuation.  Its strict subunit locus on the base ring is exactly the base
maximal ideal, and every base-ring unit has valuation one.  A prescribed
nonzero element of that maximal ideal has a nonzero valuation below one.
The valuation is constructed from the maximal ideal of the extension DVR;
no extension-valuation or detection premise is assumed. -/
theorem exists_discrete_field_valuation_above_nonzero
    (a : A) (ha : a ∈ maximalIdeal A) (hane : a ≠ 0) :
    ∃ v : Valuation F (WithZero (Multiplicative ℤ)),
      v (algebraMap A F a) < 1 ∧ v (algebraMap A F a) ≠ 0 ∧
      (∀ b : A, v (algebraMap A F b) < 1 ↔ b ∈ maximalIdeal A) ∧
      (∀ u : Aˣ, v (algebraMap A F (u : A)) = 1) := by
  obtain ⟨O, hO, hfrac, hmem⟩ := exists_discreteValuationRing_above A K F
  letI : IsDiscreteValuationRing O := hO
  letI : IsFractionRing O F := hfrac
  let w : IsDedekindDomain.HeightOneSpectrum O :=
    ⟨maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
  let v : Valuation F (WithZero (Multiplicative ℤ)) := w.valuation F
  have hstrict (b : A) :
      v (algebraMap A F b) < 1 ↔ b ∈ maximalIdeal A := by
    rw [IsScalarTower.algebraMap_apply A O F]
    exact (w.valuation_lt_one_iff_mem (K := F) (algebraMap A O b)).trans
      (hmem b).symm
  refine ⟨v, (hstrict a).mpr ha, ?_, hstrict, ?_⟩
  · apply (Valuation.ne_zero_iff v).mpr
    have hAF : Function.Injective (algebraMap A F) :=
      algebraMap_injective_of_field_isFractionRing (R := A) (S := F) K F
    intro hz
    exact hane (hAF (by simpa using hz))
  · intro u
    rw [IsScalarTower.algebraMap_apply A O F]
    change w.valuation F (algebraMap O F (algebraMap A O (u : A))) = 1
    rw [w.valuation_of_algebraMap]
    apply w.intValuation_eq_one_iff.mpr
    exact IsLocalRing.notMem_maximalIdeal.mpr (u.isUnit.map (algebraMap A O))

end ChenRanks
