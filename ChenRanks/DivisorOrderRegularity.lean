import ChenRanks.NoCodimensionOnePoles
import ChenRanks.FiniteValuationRows

/-!
# Actual height-one valuations and regularity

For an actual Noetherian integrally closed domain, this file proves that
its actual localization at a height-one prime is a discrete valuation
ring.  It constructs the normalized maximal-ideal valuation on the actual
fraction field and proves that its subunit locus is exactly that actual
localization.  Valuation one therefore means that a fraction and its
inverse both belong to the local ring.

These are the affine algebraic interfaces for the manuscript's passage
from zero divisor orders to absence of codimension-one poles.  Actual
scheme divisors and their identification with these valuations are not
yet constructed here.
-/

namespace ChenRanks

noncomputable section

open IsLocalRing Multiplicative

open scoped BigOperators

variable (A K : Type*) [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- The actual height-one prime localization of a Noetherian normal domain
is a DVR.  No local ring or dimension detector is assumed. -/
theorem height_one_primeLocalization_isDiscreteValuationRing
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1) :
    IsDiscreteValuationRing (primeLocalizationInFractionField A K p hp) := by
  classical
  letI : p.IsPrime := hp
  let S := primeLocalizationInFractionField A K p hp
  letI : IsLocalization.AtPrime S p := by
    change IsLocalization p.primeCompl
      (Localization.subalgebra K p.primeCompl p.primeCompl_le_nonZeroDivisors)
    infer_instance
  letI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  letI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim S = (1 : WithBot ℕ∞) := by
    simpa only [hheight, WithBot.coe_one] using
      IsLocalization.AtPrime.ringKrullDim_eq_height p S
  letI : FiniteRingKrullDim S :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (by
      rw [hdim]
      refine ⟨WithBot.coe_ne_bot, ?_⟩
      change ((1 : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
      intro h
      exact ENat.coe_ne_top 1 (WithBot.coe_inj.mp h))
  letI : Ring.DimensionLEOne S := ⟨by
    intro q hqne hqprime
    letI : q.IsPrime := hqprime
    have hlow : 1 ≤ q.height := by
      have h := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hqne)
      simpa only [← Ideal.height_eq_primeHeight, Ideal.height_bot, zero_add] using h
    have hupp : (q.height : WithBot ℕ∞) ≤ 1 := by
      rw [← hdim]
      exact Ideal.height_le_ringKrullDim_of_ne_top hqprime.ne_top
    have hqheight : (q.height : WithBot ℕ∞) = 1 :=
      le_antisymm hupp (by exact_mod_cast hlow)
    apply Ideal.isMaximal_of_primeHeight_eq_ringKrullDim
    simpa only [← Ideal.height_eq_primeHeight, hdim] using hqheight⟩
  letI : IsDedekindDomain S :=
    (isDedekindDomain_iff S K).mpr ⟨inferInstance, inferInstance, inferInstance,
      fun hx ↦ IsIntegrallyClosed.algebraMap_eq_of_integral hx⟩
  have hpne : p ≠ ⊥ := by
    intro h
    simp only [h, Ideal.height_bot, zero_ne_one] at hheight
  have hnf : ¬ IsField S := IsLocalization.AtPrime.not_isField A hpne S
  have hiff : IsDiscreteValuationRing S ↔ IsDedekindDomain S :=
    (IsDiscreteValuationRing.TFAE S hnf).out 0 2
  exact hiff.mpr (inferInstance : IsDedekindDomain S)

/-- The actual normalized discrete valuation of the actual height-one
localization, constructed from its maximal ideal. -/
def heightOnePrimeValuation (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1) :
    Valuation K (WithZero (Multiplicative ℤ)) := by
  let S := primeLocalizationInFractionField A K p hp
  letI : IsDiscreteValuationRing S :=
    height_one_primeLocalization_isDiscreteValuationRing A K p hp hheight
  let w : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  exact w.valuation K

/-- The actual valuation's ring of integers is exactly the actual prime
localization inside the actual fraction field. -/
theorem heightOnePrimeValuation_le_one_iff
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1) (x : K) :
    heightOnePrimeValuation A K p hp hheight x ≤ 1 ↔
      x ∈ primeLocalizationInFractionField A K p hp := by
  let S := primeLocalizationInFractionField A K p hp
  letI : IsDiscreteValuationRing S :=
    height_one_primeLocalization_isDiscreteValuationRing A K p hp hheight
  let w : IsDedekindDomain.HeightOneSpectrum S :=
    ⟨maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩
  change w.valuation K x ≤ 1 ↔ x ∈ S
  constructor
  · intro hx
    obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hdunit : IsUnit (d : S) := IsLocalRing.notMem_maximalIdeal.mp d.property
    have hdnonzero : algebraMap S K (d : S) ≠ 0 :=
      (hdunit.map (algebraMap S K)).ne_zero
    obtain ⟨u, hu⟩ := hdunit
    have hsol : algebraMap S K (n * (↑u⁻¹ : S)) = x := by
      apply mul_right_cancel₀ hdnonzero
      calc
        algebraMap S K (n * (↑u⁻¹ : S)) * algebraMap S K (d : S) =
            algebraMap S K ((n * (↑u⁻¹ : S)) * (d : S)) := (map_mul _ _ _).symm
        _ = algebraMap S K n := by rw [← hu]; simp
        _ = x * algebraMap S K (d : S) := hnd.symm
    rw [← hsol]
    exact (n * (↑u⁻¹ : S)).property
  · intro hx
    exact w.valuation_le_one (⟨x, hx⟩ : S)

/-- Actual valuation one implies that the fraction and its inverse are
both members of the actual prime localization. -/
theorem fraction_and_inverse_mem_of_heightOnePrimeValuation_eq_one
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1) (x : K)
    (hx : heightOnePrimeValuation A K p hp hheight x = 1) :
    x ∈ primeLocalizationInFractionField A K p hp ∧
      x⁻¹ ∈ primeLocalizationInFractionField A K p hp := by
  refine ⟨(heightOnePrimeValuation_le_one_iff A K p hp hheight x).mp hx.le, ?_⟩
  apply (heightOnePrimeValuation_le_one_iff A K p hp hheight x⁻¹).mp
  have hinv : heightOnePrimeValuation A K p hp hheight x⁻¹ = 1 := by
    rw [map_inv₀, hx, inv_one]
  exact hinv.le

/-- If all actual height-one valuations are one, the actual fraction and
its inverse both come from the original Noetherian normal domain. -/
theorem regular_and_inverse_regular_of_heightOnePrimeValuations_eq_one
    (x : K)
    (hx : ∀ p : Ideal A, ∀ hp : p.IsPrime, ∀ hheight : p.height = 1,
      heightOnePrimeValuation A K p hp hheight x = 1) :
    (∃ a : A, algebraMap A K a = x) ∧ (∃ b : A, algebraMap A K b = x⁻¹) := by
  apply regular_and_inverse_regular_of_no_codimension_one_poles A K x
  · intro p hp hheight
    exact (fraction_and_inverse_mem_of_heightOnePrimeValuation_eq_one
      A K p hp hheight x (hx p hp hheight)).1
  · intro p hp hheight
    exact (fraction_and_inverse_mem_of_heightOnePrimeValuation_eq_one
      A K p hp hheight x (hx p hp hheight)).2

/-- The actual integer order associated with the actual local DVR.
Its value at zero is a junk value; all divisor-order conclusions below
are stated for nonzero fractions or units.  The minus sign counts zeros
positively and poles negatively. -/
def heightOnePrimeOrder (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (x : K) : ℤ :=
  -WithZero.log (heightOnePrimeValuation A K p hp hheight x)

/-- For an actual nonzero fraction, order zero is exactly actual valuation
one.  No connection to a separately assumed geometric divisor is used. -/
theorem heightOnePrimeOrder_eq_zero_iff
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (x : K) (hxne : x ≠ 0) :
    heightOnePrimeOrder A K p hp hheight x = 0 ↔
      heightOnePrimeValuation A K p hp hheight x = 1 := by
  change -WithZero.log (heightOnePrimeValuation A K p hp hheight x) = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro hlog
    have hvne : heightOnePrimeValuation A K p hp hheight x ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hxne
    calc
      heightOnePrimeValuation A K p hp hheight x =
          WithZero.exp (WithZero.log (heightOnePrimeValuation A K p hp hheight x)) :=
        (WithZero.exp_log hvne).symm
      _ = 1 := by rw [hlog, WithZero.exp_zero]
  · intro hx
    rw [hx, WithZero.log_one]

/-- Multiplicativity of the actual local valuation gives additivity of
its actual integer order on nonzero fractions. -/
theorem heightOnePrimeOrder_mul
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    heightOnePrimeOrder A K p hp hheight (x * y) =
      heightOnePrimeOrder A K p hp hheight x +
        heightOnePrimeOrder A K p hp hheight y := by
  have hvx : heightOnePrimeValuation A K p hp hheight x ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hx
  have hvy : heightOnePrimeValuation A K p hp hheight y ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hy
  simp only [heightOnePrimeOrder, map_mul, WithZero.log_mul hvx hvy, neg_add]

/-- The actual order is a homomorphism on actual nonzero rational
functions represented as units of the fraction field. -/
def heightOnePrimeOrderHom
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1) :
    Kˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (heightOnePrimeOrder A K p hp hheight (u : K))
  map_one' := by simp [heightOnePrimeOrder]
  map_mul' u v := by
    change Multiplicative.ofAdd (heightOnePrimeOrder A K p hp hheight ((u * v : Kˣ) : K)) =
      Multiplicative.ofAdd (heightOnePrimeOrder A K p hp hheight (u : K) +
        heightOnePrimeOrder A K p hp hheight (v : K))
    rw [Units.val_mul, heightOnePrimeOrder_mul A K p hp hheight
      (u : K) (v : K) u.ne_zero v.ne_zero]

/-- The actual local order of an actual integer power. -/
theorem heightOnePrimeOrder_unit_zpow
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (u : Kˣ) (n : ℤ) :
    heightOnePrimeOrder A K p hp hheight ((u ^ n : Kˣ) : K) =
      n * heightOnePrimeOrder A K p hp hheight (u : K) := by
  have h := congrArg Multiplicative.toAdd
    (map_zpow (heightOnePrimeOrderHom A K p hp hheight) u n)
  simpa only [heightOnePrimeOrderHom, MonoidHom.coe_mk,
    toAdd_ofAdd, toAdd_zpow, zsmul_eq_mul] using h

/-- The actual local order of an actual finite product. -/
theorem heightOnePrimeOrder_unit_prod {ι : Type*}
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (s : Finset ι) (u : ι → Kˣ) :
    heightOnePrimeOrder A K p hp hheight ((∏ j ∈ s, u j : Kˣ) : K) =
      ∑ j ∈ s, heightOnePrimeOrder A K p hp hheight (u j : K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heightOnePrimeOrder]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Units.val_mul,
      heightOnePrimeOrder_mul A K p hp hheight (u j : K)
        ((∏ k ∈ s, u k : Kˣ) : K) (u j).ne_zero (∏ k ∈ s, u k : Kˣ).ne_zero,
      Finset.sum_insert hj, ih]

/-- The precise actual order identity used for integer kernel products. -/
theorem heightOnePrimeOrder_unit_prod_zpow {ι : Type*}
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1)
    (s : Finset ι) (u : ι → Kˣ) (n : ι → ℤ) :
    heightOnePrimeOrder A K p hp hheight ((∏ j ∈ s, u j ^ n j : Kˣ) : K) =
      ∑ j ∈ s, n j * heightOnePrimeOrder A K p hp hheight (u j : K) := by
  rw [heightOnePrimeOrder_unit_prod]
  simp only [heightOnePrimeOrder_unit_zpow]

/-- The actual integer rows of all actual height-one primes for a finite
family of actual nonzero rational functions. -/
def heightOnePrimeOrderRows {ι : Type*} (u : ι → Kˣ) :
    {p : Ideal A // p.IsPrime ∧ p.height = 1} → ι → ℤ :=
  fun p j ↦ heightOnePrimeOrder A K p.1 p.2.1 p.2.2 (u j : K)

/-- The integer row kernel of the actual height-one valuations proves
actual local membership and then actual regularity for a product and
its inverse.  The row system and valuation detector are constructed,
not additional hypotheses. -/
theorem regular_unit_product_of_heightOnePrime_integer_kernel
    {ι : Type*} [Fintype ι] (u : ι → Kˣ) (n : ι → ℤ)
    (hkernel : ∀ p, integerRowDot (heightOnePrimeOrderRows A K u) n p = 0) :
    (∃ a : A, algebraMap A K a = ((∏ j, u j ^ n j : Kˣ) : K)) ∧
      (∃ b : A, algebraMap A K b = (((∏ j, u j ^ n j : Kˣ) : K)⁻¹)) := by
  classical
  apply regular_and_inverse_regular_of_heightOnePrimeValuations_eq_one A K
    ((∏ j, u j ^ n j : Kˣ) : K)
  intro p hp hheight
  apply (heightOnePrimeOrder_eq_zero_iff A K p hp hheight
    ((∏ j, u j ^ n j : Kˣ) : K) (∏ j, u j ^ n j : Kˣ).ne_zero).mp
  rw [heightOnePrimeOrder_unit_prod_zpow A K p hp hheight Finset.univ u n]
  simpa only [integerRowDot, heightOnePrimeOrderRows, mul_comm] using
    hkernel ⟨p, hp, hheight⟩

end

end ChenRanks
