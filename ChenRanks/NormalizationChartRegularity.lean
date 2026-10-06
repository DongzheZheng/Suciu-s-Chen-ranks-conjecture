import ChenRanks.GenericPointFiniteNormalization
import ChenRanks.OriginalChartNormalization

/-!
# Actual normal Noetherian charts of the native normalization

The library's actual normalization section ring is compared with the
actual original-chart integral closure, using the already proved
pullback/germ triangle. Normality and Noetherianity are transported along
this constructed ring equivalence, not required of a desired model.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]

/-- The native normalization diagram's actual chart ring is the actual
closure in the original scheme field, with the original chart action. -/
def actualNormalizationChartRingEquivOriginal :
    actualNormalizationChartRing X U ≃ₐ[Γ(X, U)] originalChartNormalizationRing X U := by
  letI : Algebra Γ(X, U)
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) :=
    ((genericPointMorphism X).app U).hom.toAlgebra
  let e := (genericPointPreimageSectionIso X U).commRingCatIsoToRingEquiv
  let eA : Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.functionField :=
    { e with
      commutes' := by
        intro a
        exact congrArg (fun φ ↦ φ.hom a) (genericPointPreimageSectionIso_pullback X U) }
  exact eA.mapIntegralClosure

/-- The actual native normalization section ring, not merely its
isomorphism class, has a constructed comparison with the original closure. -/
def actualNormalizationChartSectionEquiv (hU : IsAffineOpen U) :
    Γ(actualFiniteTypeNormalization X, actualFiniteTypeNormalizationMap X ⁻¹ᵁ U) ≃+*
      originalChartNormalizationRing X U := by
  let eN : Γ(actualFiniteTypeNormalization X,
      actualFiniteTypeNormalizationMap X ⁻¹ᵁ U) ≃+* actualNormalizationChartRing X U :=
    ((genericPointMorphism X).normalizationObjIso hU).commRingCatIsoToRingEquiv
  exact eN.trans (actualNormalizationChartRingEquivOriginal X U).toRingEquiv

/-- Every such actual native chart is normal, by the actual ring comparison. -/
theorem actualNormalizationChart_isIntegrallyClosed (hU : IsAffineOpen U) :
    IsIntegrallyClosed
      Γ(actualFiniteTypeNormalization X, actualFiniteTypeNormalizationMap X ⁻¹ᵁ U) := by
  letI : IsIntegrallyClosed (originalChartNormalizationRing X U) :=
    originalChartNormalizationRing_isIntegrallyClosed X U hU
  exact IsIntegrallyClosed.of_equiv (actualNormalizationChartSectionEquiv X U hU).symm

variable {k : Type u} [Field k] [CharZero k]

/-- Finite-type input makes the actual native normalization chart Noetherian. -/
theorem actualNormalizationChart_isNoetherian
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] (hU : IsAffineOpen U) :
    IsNoetherianRing
      Γ(actualFiniteTypeNormalization X, actualFiniteTypeNormalizationMap X ⁻¹ᵁ U) := by
  letI : IsNoetherianRing (originalChartNormalizationRing X U) :=
    originalChartNormalizationRing_isNoetherian X U σ hU
  exact isNoetherianRing_of_ringEquiv (originalChartNormalizationRing X U)
    (actualNormalizationChartSectionEquiv X U hU).symm

end ChenRanks
