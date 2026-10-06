import ChenRanks.ScalarSchemeCharts

/-!
# Normal and Noetherian original chart integral closures

The original chart normalization is constructed in the original scheme
function field, using the native chart germ. Normality follows from the
actual integral closure and its actual fraction-field localization;
Noetherianity follows from proved characteristic-zero finite normalization.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]

def originalChartNormalizationRing : Type u := integralClosure Γ(X, U) X.functionField

instance originalChartNormalizationRing_commRing :
    CommRing (originalChartNormalizationRing X U) :=
  Subalgebra.toCommRing (integralClosure Γ(X, U) X.functionField)

instance originalChartNormalizationRing_isDomain :
    IsDomain (originalChartNormalizationRing X U) :=
  Subalgebra.isDomain (integralClosure Γ(X, U) X.functionField)

instance originalChartNormalizationRing_algebra :
    Algebra Γ(X, U) (originalChartNormalizationRing X U) :=
  Subalgebra.algebra (integralClosure Γ(X, U) X.functionField)

instance originalChartNormalizationRing_functionFieldAlgebra :
    Algebra (originalChartNormalizationRing X U) X.functionField :=
  Subalgebra.toAlgebra (integralClosure Γ(X, U) X.functionField)

/-- The original scheme field is also the actual chart closure's fraction field. -/
theorem originalChartNormalizationRing_isFractionRing (hU : IsAffineOpen U) :
    IsFractionRing (originalChartNormalizationRing X U) X.functionField := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsIntegralClosure.isFractionRing_of_finite_extension
    Γ(X, U) X.functionField X.functionField (integralClosure Γ(X, U) X.functionField)

/-- Normality is derived for the actual original chart closure. -/
theorem originalChartNormalizationRing_isIntegrallyClosed (hU : IsAffineOpen U) :
    IsIntegrallyClosed (originalChartNormalizationRing X U) := by
  letI : IsFractionRing (originalChartNormalizationRing X U) X.functionField :=
    originalChartNormalizationRing_isFractionRing X U hU
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField).mpr
    (inferInstance : IsIntegrallyClosedIn
      (integralClosure Γ(X, U) X.functionField) X.functionField)

variable {k : Type u} [Field k] [CharZero k]

/-- Actual finite-type input proves finiteness of this actual closure. -/
theorem originalChartNormalizationRing_finite
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) (originalChartNormalizationRing X U) :=
  originalAffineChart_integralClosure_finite σ U hU

/-- The actual original closure is Noetherian, rather than assumed to be so. -/
theorem originalChartNormalizationRing_isNoetherian
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ] (hU : IsAffineOpen U) :
    IsNoetherianRing (originalChartNormalizationRing X U) := by
  letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
  letI : Algebra.FiniteType k Γ(X, U) := chartScalarAlgebra_finiteType σ U hU
  letI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  letI : Module.Finite Γ(X, U) (originalChartNormalizationRing X U) :=
    originalChartNormalizationRing_finite X U σ hU
  exact IsNoetherianRing.of_finite Γ(X, U) (originalChartNormalizationRing X U)

end ChenRanks
