import Mathlib

/-!
# Actual localization injectivity for smooth Kähler modules

Formal smoothness gives a projective, hence flat, actual Kähler module.
The actual Kähler map to a localization is an actual localized-module
map; nonzerodivisors therefore act regularly and give injectivity.

For localizations of actual polynomial coordinate rings, formal
smoothness is derived from the polynomial and localization theorems.
It is not an additional injectivity assumption.

The general theorem that an essentially finite-type regular local ring
over a perfect field is smooth is not proved here.  In particular, the
polynomial-localization application is stated with its actual source
ring and localization structure rather than asserted for arbitrary DVRs.
-/

noncomputable section

namespace ChenRanks

section ActualLocalization

variable (C A F : Type*) [CommRing C] [CommRing A] [IsDomain A] [Field F]
  [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]
  [IsFractionRing A F]

omit [IsDomain A] in
/-- The actual Kähler map from a formally smooth domain to its actual
fraction field is injective.  The proof derives regularity from the
projectivity and flatness of its actual Kähler module. -/
theorem smooth_differential_fractionMap_injective [Algebra.FormallySmooth C A] :
    Function.Injective (KaehlerDifferential.map C C A F) := by
  apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors A)
    (KaehlerDifferential.map C C A F)).mpr
  intro s
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors s.property

end ActualLocalization

section PolynomialLocalization

variable (C : Type*) [CommRing C] (σ : Type*)
  (S : Type*) [CommRing S]
  [Algebra C S] [Algebra (MvPolynomial σ C) S]
  [IsScalarTower C (MvPolynomial σ C) S]

/-- Formal smoothness of an actual localization of an actual polynomial
coordinate ring follows from genuine polynomial and localization
smoothness.  No smoothness property of `S` is assumed. -/
theorem polynomialLocalization_formallySmooth (M : Submonoid (MvPolynomial σ C))
    [IsLocalization M S] : Algebra.FormallySmooth C S := by
  letI : Algebra.FormallySmooth (MvPolynomial σ C) S :=
    Algebra.FormallySmooth.of_isLocalization M
  exact Algebra.FormallySmooth.comp C (MvPolynomial σ C) S

variable (F : Type*) [IsDomain S] [Field F]
  [Algebra C F] [Algebra S F] [IsScalarTower C S F] [IsFractionRing S F]

omit [IsDomain S] in
/-- An actual polynomial-chart localization has an injective actual
map to the differentials of its fraction field.  All smoothness and
torsion regularity used in the proof are derived. -/
theorem polynomialLocalization_differential_fractionMap_injective
    (M : Submonoid (MvPolynomial σ C)) [IsLocalization M S] :
    Function.Injective (KaehlerDifferential.map C C S F) := by
  letI : Algebra.FormallySmooth C S := polynomialLocalization_formallySmooth C σ S M
  exact smooth_differential_fractionMap_injective C S F

end PolynomialLocalization

end ChenRanks
