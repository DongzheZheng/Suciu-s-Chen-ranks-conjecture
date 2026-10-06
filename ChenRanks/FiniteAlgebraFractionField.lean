import Mathlib

/-!
# Actual finite fraction extensions from finite algebra inclusions

For an actual finite injective algebra inclusion A → R of domains,
localizing R at the image of A's nonzero elements gives an actual
finite-dimensional algebra over Frac(A). This localization is a domain,
hence a field by integrality, and is proved to be a fraction field of R.
It is therefore canonically equivalent to any original fraction field
of R. No finite fraction extension or normalization finiteness is assumed.

This is the algebraic foundation needed for finite normalization of the
paper's actual graph model after actual Noether normalization.
-/

noncomputable section

namespace ChenRanks

variable (A R : Type*) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]

/-- The actual localization at the actual image of the base nonzero elements. -/
abbrev finiteBaseLocalization :=
  Localization (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))

/-- Actual injectivity keeps every base denominator a nonzerodivisor. -/
theorem finiteBaseSubmonoid_le_nonZeroDivisors
    (hAR : Function.Injective (algebraMap A R)) :
    Algebra.algebraMapSubmonoid R (nonZeroDivisors A) ≤ nonZeroDivisors R := by
  rintro x ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((map_ne_zero_iff (algebraMap A R) hAR).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp ha))

/-- The actual base localization is a domain, derived from its real denominators. -/
theorem finiteBaseLocalization_isDomain (hAR : Function.Injective (algebraMap A R)) :
    IsDomain (finiteBaseLocalization A R) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (finiteBaseLocalization A R) (finiteBaseSubmonoid_le_nonZeroDivisors A R hAR)

variable [Module.Finite A R]

/-- The field structure is constructed from the actual finite localized
module and the actual integral-domain criterion. -/
abbrev finiteBaseLocalizationField (hAR : Function.Injective (algebraMap A R)) :
    Field (finiteBaseLocalization A R) := by
  letI : IsDomain (finiteBaseLocalization A R) := finiteBaseLocalization_isDomain A R hAR
  letI : Module.Finite (FractionRing A) (finiteBaseLocalization A R) := inferInstance
  letI : Algebra.IsIntegral (FractionRing A) (finiteBaseLocalization A R) := inferInstance
  exact (isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing A))).toField

/-- The constructed field is genuinely a fraction field of the original
ring, by actual localization injectivity and inversion of all nonzero elements. -/
theorem finiteBaseLocalization_isFractionRing
    (hAR : Function.Injective (algebraMap A R)) :
    letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
    IsFractionRing R (finiteBaseLocalization A R) := by
  letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors R := finiteBaseSubmonoid_le_nonZeroDivisors A R hAR
  have hinj : Function.Injective (algebraMap R (finiteBaseLocalization A R)) :=
    IsLocalization.injective (finiteBaseLocalization A R) hM
  exact IsLocalization.of_le M (nonZeroDivisors R) hM fun r hr ↦
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hr))

variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual fraction comparison, not an arbitrarily supplied field equivalence. -/
def finiteBaseLocalizationFractionEquiv
    (hAR : Function.Injective (algebraMap A R)) :
    letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
    (finiteBaseLocalization A R) ≃ₐ[R] F := by
  letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
  letI : IsFractionRing R (finiteBaseLocalization A R) :=
    finiteBaseLocalization_isFractionRing A R hAR
  exact IsLocalization.algEquiv (nonZeroDivisors R) (finiteBaseLocalization A R) F

/-- The actual fraction-field base action is induced by the actual
localization comparison and the actual base localization map. -/
abbrev finiteAlgebraFractionBaseAlgebra
    (hAR : Function.Injective (algebraMap A R)) : Algebra (FractionRing A) F := by
  letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
  exact ((finiteBaseLocalizationFractionEquiv A R F hAR).toRingHom.comp
    (algebraMap (FractionRing A) (finiteBaseLocalization A R))).toAlgebra

/-- The constructed fraction action agrees with the original inclusion
on each original base element. -/
theorem finiteAlgebraFractionBaseAlgebra_algebraMap
    (hAR : Function.Injective (algebraMap A R)) (a : A) :
    letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
    algebraMap (FractionRing A) F (algebraMap A (FractionRing A) a) =
      algebraMap R F (algebraMap A R a) := by
  letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
  letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
  let e := finiteBaseLocalizationFractionEquiv A R F hAR
  change e (algebraMap (FractionRing A) (finiteBaseLocalization A R)
    (algebraMap A (FractionRing A) a)) = _
  rw [← IsScalarTower.algebraMap_apply A (FractionRing A) (finiteBaseLocalization A R),
    IsScalarTower.algebraMap_apply A R (finiteBaseLocalization A R)]
  exact e.commutes (algebraMap A R a)

/-- When the original ambient field already carries its actual base
structure, the constructed fraction action forms the actual scalar tower. -/
theorem finiteAlgebraFractionBaseScalarTower [Algebra A F] [IsScalarTower A R F]
    (hAR : Function.Injective (algebraMap A R)) :
    letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
    IsScalarTower A (FractionRing A) F := by
  letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [finiteAlgebraFractionBaseAlgebra_algebraMap]
  exact IsScalarTower.algebraMap_apply A R F a

/-- The original fraction field has a finite-dimensional base action
constructed from the original actual finite inclusion. -/
theorem finiteAlgebraFraction_finiteDimensional
    (hAR : Function.Injective (algebraMap A R)) :
    letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
    FiniteDimensional (FractionRing A) F := by
  letI : Field (finiteBaseLocalization A R) := finiteBaseLocalizationField A R hAR
  letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
  let e := finiteBaseLocalizationFractionEquiv A R F hAR
  let eK : (finiteBaseLocalization A R) ≃ₗ[FractionRing A] F :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change e (algebraMap (FractionRing A) (finiteBaseLocalization A R) a * x) =
          e (algebraMap (FractionRing A) (finiteBaseLocalization A R) a) * e x
        exact map_mul e _ _ }
  exact Module.Finite.of_surjective eK.toLinearMap eK.surjective

end ChenRanks
