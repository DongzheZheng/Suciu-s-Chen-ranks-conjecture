import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Native quotient-ring localizations and actual localized ideal quotients

The scalar action is the genuine quotient of the original localization
homomorphism. The localization universal property is proved using the
actual two quotient maps, their genuine kernels, and their surjectivity.
For a prime containing the original ideal, the actual image of its
prime-complement submonoid is proved equal to the true quotient prime's
complement. This identifies the two native rings without identifying
distinct primes in the original ring.
-/

noncomputable section

namespace ChenRanks

section Localization

variable (R : Type*) [CommRing R] (D : Submonoid R)
variable (A : Type*) [CommRing A] [Algebra R A] [hA : IsLocalization D A]
variable (J : Ideal R)

/-- The actual canonical quotient of the localization coefficient map. -/
@[implicit_reducible] def localizedIdealQuotientAlgebra :
    Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

local instance quotientLocalizationAlgebra :
    Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) :=
  localizedIdealQuotientAlgebra R A J

include D hA

/-- Quotienting a genuine localization by the extension of the actual
original ideal gives a genuine localization of the actual original
quotient, at the actual mapped denominator submonoid. -/
theorem localizedIdealQuotient_isLocalization :
    IsLocalization (D.map (Ideal.Quotient.mk J))
      (A ⧸ J.map (algebraMap R A)) := by
  apply IsLocalization.of_surjective D A
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (J.map (algebraMap R A))) Ideal.Quotient.mk_surjective
  · exact (Ideal.quotientMap_comp_mk (f := algebraMap R A) Ideal.le_comap_map).symm
  · rw [Ideal.mk_ker, Ideal.mk_ker]

/-- The native localization of the original quotient is genuinely
isomorphic to the quotient of the actual original localization. -/
def quotientLocalizationRingEquiv :
    Localization (D.map (Ideal.Quotient.mk J)) ≃+*
      (A ⧸ J.map (algebraMap R A)) := by
  letI := localizedIdealQuotient_isLocalization R D A J
  exact (IsLocalization.algEquiv (D.map (Ideal.Quotient.mk J))
    (Localization (D.map (Ideal.Quotient.mk J)))
    (A ⧸ J.map (algebraMap R A))).toRingEquiv

end Localization

section Primes

variable (R : Type*) [CommRing R]

/-- The actual image prime in the actual quotient ring. Its primality
is derived from the surjective quotient map and the true containment. -/
def quotientPrimePoint (J q : Ideal R) [q.IsPrime] (hJq : J ≤ q) :
    PrimeSpectrum (R ⧸ J) :=
  ⟨q.map (Ideal.Quotient.mk J),
    Ideal.isPrime_map_quotientMk_of_isPrime hJq⟩

/-- The actual quotient prime contracts to the original prime. -/
theorem quotientPrimePoint_comap (J q : Ideal R) [q.IsPrime] (hJq : J ≤ q) :
    (quotientPrimePoint R J q hJq).asIdeal.comap (Ideal.Quotient.mk J) = q := by
  exact Ideal.comap_map_mk hJq

/-- Surjectivity and actual prime contraction identify the actual
mapped denominator submonoid with the true target prime complement. -/
theorem map_primeComplement_eq_of_surjective
    (B : Type*) [CommRing B] (f : R →+* B) (hf : Function.Surjective f)
    (q : Ideal R) [q.IsPrime] (p : Ideal B) [p.IsPrime]
    (hqp : p.comap f = q) : q.primeCompl.map f = p.primeCompl := by
  have hmem : ∀ r : R, r ∈ q ↔ f r ∈ p := by
    intro r
    rw [← hqp]
    rfl
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    intro hp
    exact hr ((hmem r).mpr hp)
  · intro hx
    obtain ⟨r, rfl⟩ := hf x
    exact ⟨r, (fun hr ↦ hx ((hmem r).mp hr)), rfl⟩

variable (A : Type*) [CommRing A] [Algebra R A]

/-- The true native localization at the quotient prime is isomorphic
to the actual localization quotient at the original prime. -/
def quotientPrimeLocalizationRingEquiv
    (J q : Ideal R) [q.IsPrime] (hJq : J ≤ q) [IsLocalization.AtPrime A q] :
    Localization.AtPrime (quotientPrimePoint R J q hJq).asIdeal ≃+*
      (A ⧸ J.map (algebraMap R A)) := by
  letI : (quotientPrimePoint R J q hJq).asIdeal.IsPrime :=
    (quotientPrimePoint R J q hJq).isPrime
  letI := localizedIdealQuotientAlgebra R A J
  have hD : q.primeCompl.map (Ideal.Quotient.mk J) =
      (quotientPrimePoint R J q hJq).asIdeal.primeCompl :=
    map_primeComplement_eq_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective q (quotientPrimePoint R J q hJq).asIdeal
        (quotientPrimePoint_comap R J q hJq)
  letI : IsLocalization (quotientPrimePoint R J q hJq).asIdeal.primeCompl
      (A ⧸ J.map (algebraMap R A)) := by
    rw [← hD]
    exact localizedIdealQuotient_isLocalization R q.primeCompl A J
  exact (IsLocalization.algEquiv (quotientPrimePoint R J q hJq).asIdeal.primeCompl
    (Localization.AtPrime (quotientPrimePoint R J q hJq).asIdeal)
    (A ⧸ J.map (algebraMap R A))).toRingEquiv

/-- Primality of the true localized extended ideal makes the actual
native quotient-prime local ring a domain, via the proved ring isomorphism. -/
theorem quotientPrimeLocalization_isDomain
    (J q : Ideal R) [q.IsPrime] (hJq : J ≤ q) [IsLocalization.AtPrime A q]
    (hprime : (J.map (algebraMap R A)).IsPrime) :
    IsDomain (Localization.AtPrime (quotientPrimePoint R J q hJq).asIdeal) := by
  letI := hprime
  letI : IsDomain (A ⧸ J.map (algebraMap R A)) := inferInstance
  exact MulEquiv.isDomain (A ⧸ J.map (algebraMap R A))
    (quotientPrimeLocalizationRingEquiv R A J q hJq).toMulEquiv

end Primes

end ChenRanks
