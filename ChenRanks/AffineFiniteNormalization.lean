import ChenRanks.FiniteTypeNormalization
import ChenRanks.DivisorOrderRegularity
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Actual finite normalization of original affine charts

The ring and morphism here are the integral closure of the original
domain in its actual fraction field and the actual spectrum of its
algebra map. Finiteness comes from characteristic-zero Noether
normalization, not from a normalization-finiteness premise. The native
fraction comparison also proves integral closedness of this actual ring.

These are affine charts for the normal graph model in the manuscript.
Gluing the charts and comparing the global normalization morphism remain
separate obligations; this file does not assert their completion.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

universe u

variable (S : Type u) [CommRing S] [IsDomain S]

/-- The actual integral closure in the original domain's actual fraction field. -/
def affineNormalizationRing : Type u := integralClosure S (FractionRing S)

instance affineNormalizationRing_commRing : CommRing (affineNormalizationRing S) :=
  Subalgebra.toCommRing (integralClosure S (FractionRing S))

instance affineNormalizationRing_isDomain : IsDomain (affineNormalizationRing S) :=
  Subalgebra.isDomain (integralClosure S (FractionRing S))

instance affineNormalizationRing_algebra : Algebra S (affineNormalizationRing S) :=
  Subalgebra.algebra (integralClosure S (FractionRing S))

instance affineNormalizationRing_fractionAlgebra :
    Algebra (affineNormalizationRing S) (FractionRing S) :=
  Subalgebra.toAlgebra (integralClosure S (FractionRing S))

/-- The original fraction field is also the actual normalized ring's fraction field. -/
instance affineNormalizationRing_isFractionRing :
    IsFractionRing (affineNormalizationRing S) (FractionRing S) :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    S (FractionRing S) (FractionRing S) (integralClosure S (FractionRing S))

/-- Integral closedness is proved for the original constructed ring. -/
instance affineNormalizationRing_isIntegrallyClosed :
    IsIntegrallyClosed (affineNormalizationRing S) :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)).mpr
    (inferInstance : IsIntegrallyClosedIn
      (integralClosure S (FractionRing S)) (FractionRing S))

/-- The actual affine normalization scheme. -/
abbrev affineNormalizationScheme : Scheme.{u} :=
  Spec (.of (affineNormalizationRing S))

/-- The actual normalization morphism on the original affine chart. -/
def affineNormalizationMap : affineNormalizationScheme S ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (affineNormalizationRing S)))

instance affineNormalizationScheme_isIntegral : IsIntegral (affineNormalizationScheme S) := by
  infer_instance

instance affineNormalizationScheme_functionFieldAlgebra :
    Algebra (affineNormalizationRing S) (affineNormalizationScheme S).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of (affineNormalizationRing S))

instance affineNormalizationScheme_functionFieldIsFractionRing :
    IsFractionRing (affineNormalizationRing S) (affineNormalizationScheme S).functionField :=
  functionField_isFractionRing_of_affine (.of (affineNormalizationRing S))

/-- The comparison is canonically constructed from the actual coordinate
localizations; an abstract field isomorphism is not an input. -/
def affineNormalizationFunctionFieldEquiv :
    (affineNormalizationScheme S).functionField ≃ₐ[affineNormalizationRing S] FractionRing S :=
  IsLocalization.algEquiv (nonZeroDivisors (affineNormalizationRing S))
    (affineNormalizationScheme S).functionField (FractionRing S)

@[simp]
theorem affineNormalizationFunctionFieldEquiv_algebraMap (x : affineNormalizationRing S) :
    affineNormalizationFunctionFieldEquiv S
        (algebraMap (affineNormalizationRing S) (affineNormalizationScheme S).functionField x) =
      algebraMap (affineNormalizationRing S) (FractionRing S) x :=
  (affineNormalizationFunctionFieldEquiv S).commutes x

section FiniteType

variable (k : Type u) [Field k] [CharZero k] [Algebra k S] [Algebra.FiniteType k S]

include k

/-- Actual finite-type characteristic-zero input proves actual normalization finiteness. -/
theorem affineNormalizationRing_finite : Module.Finite S (affineNormalizationRing S) :=
  finiteType_integralClosure_finite k S (FractionRing S)

/-- The resulting actual affine normalization morphism is finite. -/
theorem affineNormalizationMap_isFinite : IsFinite (affineNormalizationMap S) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (affineNormalizationRing_finite S k)

/-- Properness is a consequence of the proved finite map. -/
theorem affineNormalizationMap_isProper : IsProper (affineNormalizationMap S) := by
  letI : IsFinite (affineNormalizationMap S) := affineNormalizationMap_isFinite S k
  infer_instance

/-- The constructed original normalization chart is actually Noetherian. -/
theorem affineNormalizationRing_isNoetherian : IsNoetherianRing (affineNormalizationRing S) := by
  letI : Module.Finite S (affineNormalizationRing S) := affineNormalizationRing_finite S k
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  exact IsNoetherianRing.of_finite S (affineNormalizationRing S)

/-- Each actual height-one prime of this constructed chart gives the
actual DVR required by the paper's codimension-one residue argument. -/
theorem affineNormalization_heightOne_isDiscreteValuationRing
    (p : Ideal (affineNormalizationRing S)) (hp : p.IsPrime) (hheight : p.height = 1) :
    IsDiscreteValuationRing
      (primeLocalizationInFractionField (affineNormalizationRing S) (FractionRing S) p hp) := by
  letI : IsNoetherianRing (affineNormalizationRing S) :=
    affineNormalizationRing_isNoetherian S k
  exact height_one_primeLocalization_isDiscreteValuationRing
    (affineNormalizationRing S) (FractionRing S) p hp hheight

end FiniteType

end ChenRanks
