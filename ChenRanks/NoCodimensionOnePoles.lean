import Mathlib

/-!
# Regularity from the absence of codimension-one poles

This is the affine commutative-algebra step used in the manuscript's
`Integral valuation kernels and vertical functions` lemma.  The ring is an
actual Noetherian integrally closed domain and the ambient field is its
actual fraction field.  The local rings are actual localizations represented
inside that field.  Their intersection formula is proved, not assumed.

The proof finds an associated prime of the class of a fraction modulo the
base ring.  The determinant trick and integral closedness show that the
denominator prime is minimal over a principal ideal, hence has height one.
This file does not yet glue affine regular functions on the manuscript's
open variety or construct its divisor orders.
-/

namespace ChenRanks

noncomputable section

variable (A K : Type*) [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The actual localization at a prime, represented as a subalgebra of the
actual fraction field. -/
def primeLocalizationInFractionField (p : Ideal A) (hp : p.IsPrime) : Subalgebra A K := by
  letI : p.IsPrime := hp
  exact Localization.subalgebra K p.primeCompl p.primeCompl_le_nonZeroDivisors

/-- Membership in the actual localization supplies an actual denominator
outside the prime which clears the fraction. -/
theorem clears_denominator_of_mem_primeLocalization
    (p : Ideal A) (hp : p.IsPrime) (x : K)
    (hx : x ∈ primeLocalizationInFractionField A K p hp) :
    ∃ s : A, s ∉ p ∧ ∃ a : A, algebraMap A K s * x = algebraMap A K a := by
  letI : p.IsPrime := hp
  change (∃ a s : A, ∃ hs : s ∈ p.primeCompl,
    x = IsLocalization.mk' K a ⟨s, p.primeCompl_le_nonZeroDivisors hs⟩) at hx
  obtain ⟨a, s, hs, hxs⟩ := hx
  have hs0 : algebraMap A K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors hs)
  refine ⟨s, hs, a, ?_⟩
  rw [hxs, IsFractionRing.mk'_eq_div]
  field_simp

private def fractionBaseSubmodule : Submodule A K :=
  LinearMap.range (Algebra.ofId A K).toLinearMap

omit [IsDomain A] [IsFractionRing A K] in
private theorem mem_fractionBaseSubmodule (x : K) :
    x ∈ fractionBaseSubmodule A K ↔ ∃ a : A, algebraMap A K a = x := Iff.rfl

/-- An actual prime annihilator of a nonregular fraction has height one.
The denominator-ideal description is used only as an intermediate lemma;
it is constructed from an actual associated prime below. -/
theorem prime_denominator_height_one [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) (hp : p.IsPrime) (z : K)
    (hz : ¬ ∃ a : A, algebraMap A K a = z)
    (hden : ∀ d : A, d ∈ p ↔ ∃ e : A, algebraMap A K e = algebraMap A K d * z) :
    p.height = 1 := by
  classical
  letI : p.IsPrime := hp
  let f : A →ₗ[A] K := (Algebra.ofId A K).toLinearMap
  let N : Submodule A K := Submodule.map f p
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective A z
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hdK0 : algebraMap A K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hdp : d ∈ p := (hden d).mpr ⟨c, by rw [← hcd]; field_simp⟩
  have hpne : p ≠ ⊥ := by
    intro h
    exact hd0 (by simpa [h] using hdp)
  have hNne : N ≠ ⊥ := by
    intro hN
    have hm : algebraMap A K d ∈ N := Submodule.mem_map_of_mem hdp
    have hzero : algebraMap A K d = 0 := by simpa [hN] using hm
    exact hdK0 hzero
  have hNfg : N.FG := Submodule.FG.map f (p.fg_of_isNoetherianRing)
  have hnotstable : ¬ ∀ a : A, a ∈ p → algebraMap A K a * z ∈ N := by
    intro hstable
    have hzint : IsIntegral A z :=
      isIntegral_of_smul_mem_submodule N hNne hNfg z (by
        intro n hn
        obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hn
        change z * algebraMap A K a ∈ N
        simpa only [mul_comm] using hstable a ha)
    exact hz (IsIntegrallyClosed.algebraMap_eq_of_integral hzint)
  push Not at hnotstable
  obtain ⟨a, hap, hapos⟩ := hnotstable
  obtain ⟨b, hb⟩ := (hden a).mp hap
  have hbnot : b ∉ p := by
    intro hbp
    have hbN : algebraMap A K b ∈ N := Submodule.mem_map_of_mem hbp
    exact hapos (hb ▸ hbN)
  have hmin : p ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hp, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hap)⟩, ?_⟩
    intro q hq hqp
    letI : q.IsPrime := hq.1
    intro t htp
    obtain ⟨e, he⟩ := (hden t).mp htp
    have hbnotq : b ∉ q := fun hbq ↦ hbnot (hqp hbq)
    have hmul : b * t = a * e := by
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul, hb, he]
      ring
    have haq : a ∈ q := hq.2 (Ideal.subset_span (by simp))
    have hbtq : b * t ∈ q := by
      rw [hmul]
      exact q.mul_mem_right e haq
    exact (hq.1.mem_or_mem hbtq).resolve_left hbnotq
  have hup : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) p hmin
  have hlow : 1 ≤ p.height := by
    have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hpne)
    simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h
  exact le_antisymm hup hlow

/-- A fraction outside a Noetherian normal domain has a genuine pole at
an actual height-one prime localization. -/
theorem exists_height_one_localization_missing [IsNoetherianRing A] [IsIntegrallyClosed A]
    (x : K) (hx : ¬ ∃ a : A, algebraMap A K a = x) :
    ∃ p : Ideal A, ∃ hp : p.IsPrime, p.height = 1 ∧
      x ∉ primeLocalizationInFractionField A K p hp := by
  classical
  let N : Submodule A K := fractionBaseSubmodule A K
  let M := K ⧸ N
  let xm : M := N.mkQ x
  have hzero_iff (w : K) : N.mkQ w = 0 ↔ w ∈ N := by
    change w ∈ LinearMap.ker N.mkQ ↔ w ∈ N
    rw [Submodule.ker_mkQ]
  have hxm : xm ≠ 0 := by
    intro h
    exact hx ((mem_fractionBaseSubmodule A K x).mp ((hzero_iff x).mp h))
  obtain ⟨p, hp, hann⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A xm hxm
  obtain ⟨hpprime, y, hpeq⟩ := isAssociatedPrime_iff.mp hp
  letI : p.IsPrime := hpprime
  obtain ⟨z, hz⟩ := N.mkQ_surjective y
  have hden (d : A) : d ∈ p ↔ ∃ e : A, algebraMap A K e = algebraMap A K d * z := by
    rw [hpeq, Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← hz, ← map_smul, hzero_iff]
    simpa only [Algebra.smul_def] using mem_fractionBaseSubmodule A K (d • z)
  have hznot : ¬ ∃ a : A, algebraMap A K a = z := by
    intro hzbase
    have h1 : (1 : A) ∈ p := (hden 1).mpr (by simpa using hzbase)
    apply hpprime.ne_top
    exact top_unique (fun a _ ↦ by simpa only [mul_one] using p.mul_mem_left a h1)
  have hheight : p.height = 1 := prime_denominator_height_one A K p hpprime z hznot hden
  refine ⟨p, hpprime, hheight, ?_⟩
  intro hxloc
  obtain ⟨s, hs, a, hsa⟩ := clears_denominator_of_mem_primeLocalization A K p hpprime x hxloc
  apply hs
  apply hann
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change s • N.mkQ x = 0
  rw [← map_smul, hzero_iff]
  rw [Algebra.smul_def]
  exact (mem_fractionBaseSubmodule A K _).mpr ⟨a, hsa.symm⟩

/-- The affine no-codimension-one-poles theorem used in the manuscript.
All localizations in the hypothesis are actual rings inside the fraction
field; no intersection or pole-detection principle is assumed. -/
theorem regular_of_no_codimension_one_poles [IsNoetherianRing A] [IsIntegrallyClosed A]
    (x : K)
    (hx : ∀ p : Ideal A, ∀ hp : p.IsPrime, p.height = 1 →
      x ∈ primeLocalizationInFractionField A K p hp) :
    ∃ a : A, algebraMap A K a = x := by
  by_contra h
  obtain ⟨p, hp, hheight, hmissing⟩ := exists_height_one_localization_missing A K x h
  exact hmissing (hx p hp hheight)

/-- The actual normal Noetherian domain is the intersection of its actual
height-one localizations inside its actual fraction field. -/
theorem base_eq_iInf_height_one_localizations [IsNoetherianRing A] [IsIntegrallyClosed A] :
    (⊥ : Subalgebra A K) =
      ⨅ p : {p : Ideal A // p.IsPrime ∧ p.height = 1},
        primeLocalizationInFractionField A K p.1 p.2.1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hx
    apply Algebra.mem_iInf.mpr
    intro p
    exact (primeLocalizationInFractionField A K p.1 p.2.1).algebraMap_mem a
  · intro hx
    apply Algebra.mem_bot.mpr
    apply regular_of_no_codimension_one_poles A K x
    intro p hp hheight
    exact Algebra.mem_iInf.mp hx ⟨p, hp, hheight⟩

/-- Applying the same actual regularity theorem to a fraction and its
inverse proves both are regular.  For the manuscript the fraction is a
nonzero integer product of the logarithmic generators. -/
theorem regular_and_inverse_regular_of_no_codimension_one_poles
    [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (hx : ∀ p : Ideal A, ∀ hp : p.IsPrime, p.height = 1 →
      x ∈ primeLocalizationInFractionField A K p hp)
    (hinv : ∀ p : Ideal A, ∀ hp : p.IsPrime, p.height = 1 →
      x⁻¹ ∈ primeLocalizationInFractionField A K p hp) :
    (∃ a : A, algebraMap A K a = x) ∧ (∃ b : A, algebraMap A K b = x⁻¹) :=
  ⟨regular_of_no_codimension_one_poles A K x hx,
    regular_of_no_codimension_one_poles A K x⁻¹ hinv⟩

end

end ChenRanks
