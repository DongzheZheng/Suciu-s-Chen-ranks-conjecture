import ChenRanks.DivisorOrderRegularity

/-!
# Finiteness of actual affine height-one order support

For a Noetherian domain, height-one primes containing a nonzero element
are actual minimal primes over its principal ideal and hence form a
finite set. For a normal Noetherian domain, the actual height-one order
of a fraction can be nonzero only at primes containing its numerator or
denominator. This proves the actual affine finiteness required when the
manuscript removes images of vertical divisor support.

The identification of these primes with model divisors and the deletion
of their images under the actual curve morphism remain separate steps.
-/

namespace ChenRanks

noncomputable section

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- Actual height-one primes containing a nonzero element are finite. -/
theorem finite_heightOnePrimes_containing (a : A) (ha : a ≠ 0) :
    {p : Ideal A | p.IsPrime ∧ p.height = 1 ∧ a ∈ p}.Finite := by
  apply (Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.subset
  rintro p ⟨hp, hh, hap⟩
  letI : p.IsPrime := hp
  have hspan : (⊥ : Ideal A) < Ideal.span {a} := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    apply ha
    exact Ideal.mem_bot.mp (h ▸ Ideal.mem_span_singleton_self a)
  have hpos : (0 : ℕ∞) < (Ideal.span {a}).height := by
    simpa only [Ideal.height_bot] using Ideal.height_strict_mono_of_is_prime hspan
  have hone : (1 : ℕ∞) ≤ (Ideal.span {a}).height := by
    simpa using (ENat.add_one_le_iff (show (0 : ℕ∞) ≠ ⊤ by simp)).mpr hpos
  have hle : Ideal.span {a} ≤ p := Ideal.span_le.mpr (by
    intro b hb
    have hba : b = a := Set.mem_singleton_iff.mp hb
    subst b
    exact hap)
  exact Ideal.mem_minimalPrimes_of_height_eq hle (by simpa only [hh] using hone)

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A]

/-- Outside the actual prime, a ring element is a unit in the actual
localization, so its actual normalized valuation is one. -/
theorem heightOnePrimeValuation_algebraMap_eq_one_of_not_mem
    (p : Ideal A) (hp : p.IsPrime) (hh : p.height = 1) (a : A) (ha : a ∉ p) :
    heightOnePrimeValuation A K p hp hh (algebraMap A K a) = 1 := by
  letI : p.IsPrime := hp
  let S := primeLocalizationInFractionField A K p hp
  letI : IsLocalization.AtPrime S p := by
    change IsLocalization p.primeCompl
      (Localization.subalgebra K p.primeCompl p.primeCompl_le_nonZeroDivisors)
    infer_instance
  letI : IsDiscreteValuationRing S :=
    height_one_primeLocalization_isDiscreteValuationRing A K p hp hh
  let w : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨IsLocalRing.maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  have hunit : IsUnit (algebraMap A S a) :=
    IsLocalization.map_units S (⟨a, ha⟩ : p.primeCompl)
  obtain ⟨u, hu⟩ := hunit
  have hprod : w.valuation K (algebraMap S K (u : S)) *
      w.valuation K (algebraMap S K (u⁻¹ : Sˣ)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  have hge : 1 ≤ w.valuation K (algebraMap S K (u : S)) := by
    calc
      1 = w.valuation K (algebraMap S K (u : S)) *
          w.valuation K (algebraMap S K (u⁻¹ : Sˣ)) := hprod.symm
      _ ≤ w.valuation K (algebraMap S K (u : S)) * 1 :=
        mul_le_mul_right (w.valuation_le_one (u⁻¹ : Sˣ)) _
      _ = w.valuation K (algebraMap S K (u : S)) := mul_one _
  have hone := le_antisymm (w.valuation_le_one (u : S)) hge
  change w.valuation K (algebraMap S K (algebraMap A S a)) = 1
  rw [← hu]
  exact hone

/-- The nonzero-order support of an actual nonzero rational function
is finite. Its support is detected by actual DVR orders, not defined to
be an arbitrary finite list. -/
theorem finite_fraction_heightOnePrimeOrder_support (f : Kˣ) :
    {p : {p : Ideal A // p.IsPrime ∧ p.height = 1} |
      heightOnePrimeOrder A K p.val p.property.1 p.property.2 (f : K) ≠ 0}.Finite := by
  classical
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (f : K)
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_div] at hab
    exact f.ne_zero hab.symm
  have hbne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hfinite := (finite_heightOnePrimes_containing A a ha).union
    (finite_heightOnePrimes_containing A b hbne)
  apply (hfinite.preimage (fun _ _ _ _ heq ↦ Subtype.val_injective heq)).subset
  intro p horder
  by_contra hnot
  have ha_not : a ∉ p.val := by
    intro h
    exact hnot (Or.inl ⟨p.property.1, p.property.2, h⟩)
  have hb_not : b ∉ p.val := by
    intro h
    exact hnot (Or.inr ⟨p.property.1, p.property.2, h⟩)
  apply horder
  apply (heightOnePrimeOrder_eq_zero_iff A K p.val p.property.1 p.property.2
    (f : K) f.ne_zero).mpr
  rw [← hab, map_div₀,
    heightOnePrimeValuation_algebraMap_eq_one_of_not_mem A K p.val p.property.1 p.property.2 a ha_not,
    heightOnePrimeValuation_algebraMap_eq_one_of_not_mem A K p.val p.property.1 p.property.2 b hb_not,
    one_div_one]

end

end ChenRanks
