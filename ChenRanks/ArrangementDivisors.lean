import ChenRanks.ArrangementDifferentials
import ChenRanks.DivisorOrderRegularity
import ChenRanks.SmoothDifferentialLocalization
import ChenRanks.DivisorSupportFinite

/-!
# Actual affine hyperplane prime divisors

The equations of the original arrangement have genuine total degree one,
so their actual principal ideals are prime and have height one. The actual
prime-localization DVR and actual smooth Kähler localization then apply
to these original hyperplanes, rather than to formal divisor labels.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual affine linear equation has genuine total degree one. -/
theorem equationPolynomial_totalDegree (H : ι) :
    (A.equationPolynomial H).totalDegree = 1 := by
  classical
  have hh : MvPolynomial.IsHomogeneous
      (∑ i : Fin d, MvPolynomial.C (A.normal H (Pi.single i 1)) * MvPolynomial.X i) 1 := by
    apply (MvPolynomial.homogeneousSubmodule (Fin d) ℂ 1).sum_mem
    intro i _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have hle : (A.equationPolynomial H).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_sub_C_le _ _).trans hh.totalDegree_le
  have hne : (A.equationPolynomial H).totalDegree ≠ 0 := by
    intro hzero
    let c := (A.equationPolynomial H).coeff 0
    have hc : A.equationPolynomial H = MvPolynomial.C c :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    have hc0 : c = -A.offset H := by
      have he := A.equationPolynomial_eval H 0
      rw [hc, MvPolynomial.eval_C] at he
      simpa using he
    apply A.normal_ne_zero H
    apply LinearMap.ext
    intro x
    have he := A.equationPolynomial_eval H x
    rw [hc, MvPolynomial.eval_C, hc0] at he
    have hx : (0 : ℂ) - A.offset H = A.normal H x - A.offset H := by simpa using he
    exact (sub_left_inj.mp hx).symm
  omega

/-- The original actual hyperplane equation is irreducible. -/
theorem equationPolynomial_irreducible (H : ι) : Irreducible (A.equationPolynomial H) := by
  apply MvPolynomial.irreducible_of_totalDegree_eq_one (A.equationPolynomial_totalDegree H)
  intro r hr
  by_cases hzero : r = 0
  · subst r
    have hz : A.equationPolynomial H = 0 := by
      apply MvPolynomial.ext
      intro m
      exact zero_dvd_iff.mp (hr m)
    exact (A.equationPolynomial_ne_zero H hz).elim
  · exact isUnit_iff_ne_zero.mpr hzero

/-- The actual ideal of an actual hyperplane. -/
def hyperplanePrimeIdeal (H : ι) : Ideal (CoordinateRing (d := d)) :=
  Ideal.span {A.equationPolynomial H}

instance hyperplanePrimeIdeal_isPrime (H : ι) : (A.hyperplanePrimeIdeal H).IsPrime :=
  (Ideal.span_singleton_prime (A.equationPolynomial_ne_zero H)).mpr
    (A.equationPolynomial_irreducible H).prime

/-- This principal prime has actual height one, by the principal ideal theorem. -/
theorem hyperplanePrimeIdeal_height (H : ι) : (A.hyperplanePrimeIdeal H).height = 1 := by
  let p := A.hyperplanePrimeIdeal H
  letI : p.IsPrincipal := by
    change (Ideal.span {A.equationPolynomial H}).IsPrincipal
    infer_instance
  have hself : p ∈ p.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton p
  have hle : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes p p hself
  have hlt : (⊥ : Ideal (CoordinateRing (d := d))) < p := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    exact A.equationPolynomial_ne_zero H
      (Ideal.mem_bot.mp (h ▸ Ideal.mem_span_singleton_self (A.equationPolynomial H)))
  have hpos : (0 : ℕ∞) < p.height := by
    simpa only [Ideal.height_bot] using Ideal.height_strict_mono_of_is_prime hlt
  have hge : (1 : ℕ∞) ≤ p.height := by
    simpa using (ENat.add_one_le_iff (show (0 : ℕ∞) ≠ ⊤ by simp)).mpr hpos
  exact le_antisymm hle hge

/-- Actual polynomial divisibility implies containment of the original
hyperplane zero sets, by their original affine equations. -/
theorem equation_zeroSet_subset_of_dvd (H K : ι)
    (h : A.equationPolynomial H ∣ A.equationPolynomial K) :
    {x : Fin d → ℂ | A.normal H x = A.offset H} ⊆
      {x : Fin d → ℂ | A.normal K x = A.offset K} := by
  intro x hx
  obtain ⟨q, hq⟩ := h
  have hH : MvPolynomial.eval x (A.equationPolynomial H) = 0 := by
    rw [equationPolynomial_eval, hx, sub_self]
  have hK : MvPolynomial.eval x (A.equationPolynomial K) = 0 := by
    rw [hq, map_mul, hH, zero_mul]
  exact sub_eq_zero.mp ((A.equationPolynomial_eval K x).symm.trans hK)

/-- Distinct actual hyperplanes have actual nonassociated irreducible equations. -/
theorem equationPolynomial_not_dvd_of_ne (H K : ι) (hHK : H ≠ K) :
    ¬A.equationPolynomial H ∣ A.equationPolynomial K := by
  intro h
  have ha := (A.equationPolynomial_irreducible H).associated_of_dvd
    (A.equationPolynomial_irreducible K) h
  apply A.distinct hHK
  exact Set.Subset.antisymm (A.equation_zeroSet_subset_of_dvd H K ha.dvd)
    (A.equation_zeroSet_subset_of_dvd K H ha.symm.dvd)

/-- A different original equation is not in this original prime ideal. -/
theorem equationPolynomial_not_mem_hyperplanePrimeIdeal
    (H K : ι) (hHK : H ≠ K) : A.equationPolynomial K ∉ A.hyperplanePrimeIdeal H := by
  change A.equationPolynomial K ∉ Ideal.span {A.equationPolynomial H}
  rw [Ideal.mem_span_singleton]
  exact A.equationPolynomial_not_dvd_of_ne H K hHK

/-- The actual normalized order of every different original equation is zero. -/
theorem hyperplaneOrder_other_equation_zero (H K : ι) (hHK : H ≠ K) :
    heightOnePrimeOrder (CoordinateRing (d := d)) (RationalFunctionField (d := d))
      (A.hyperplanePrimeIdeal H) (A.hyperplanePrimeIdeal_isPrime H)
      (A.hyperplanePrimeIdeal_height H) (A.equationFunction K) = 0 := by
  apply (heightOnePrimeOrder_eq_zero_iff (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (A.hyperplanePrimeIdeal H)
    (A.hyperplanePrimeIdeal_isPrime H) (A.hyperplanePrimeIdeal_height H)
    (A.equationFunction K) (A.equationFunction_ne_zero K)).mpr
  exact heightOnePrimeValuation_algebraMap_eq_one_of_not_mem
    (CoordinateRing (d := d)) (RationalFunctionField (d := d))
    (A.hyperplanePrimeIdeal H) (A.hyperplanePrimeIdeal_isPrime H)
    (A.hyperplanePrimeIdeal_height H) (A.equationPolynomial K)
    (A.equationPolynomial_not_mem_hyperplanePrimeIdeal H K hHK)

/-- The actual hyperplane local ring inside the original actual rational field. -/
abbrev hyperplaneLocalRing (H : ι) :=
  primeLocalizationInFractionField (CoordinateRing (d := d)) (RationalFunctionField (d := d))
    (A.hyperplanePrimeIdeal H) (A.hyperplanePrimeIdeal_isPrime H)

instance hyperplaneLocalRing_isDiscreteValuationRing (H : ι) :
    IsDiscreteValuationRing (A.hyperplaneLocalRing H) :=
  height_one_primeLocalization_isDiscreteValuationRing
    (CoordinateRing (d := d)) (RationalFunctionField (d := d))
    (A.hyperplanePrimeIdeal H) (A.hyperplanePrimeIdeal_isPrime H)
    (A.hyperplanePrimeIdeal_height H)

end ChenRanks.AffineArrangement
