import ChenRanks.ArrangementCurvePullbackStatements
import ChenRanks.RationalFunctionNativeScalarTower
import ChenRanks.ProjectiveOriginalScalarActions

/-!
# Constructed scalar data of the actual coefficient curve

The record contains field and scalar structures, rather than a separation
conclusion or an existence assumption. Its actual instance is constructed
from the original coefficient intermediate field and the already proved
finite rational-function extension. All actions are induced by the actual
algebra maps.
-/

noncomputable section

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule

/-- Actual field and scalar data used by the coefficient-curve model.
No geometric model, separation, or differential detection is a field. -/
structure CoefficientCurveScalarContext (d : ℕ) where
  L : Type
  [field : Field L]
  [complexAlgebra : Algebra ℂ L]
  [originalAlgebra : Algebra L (AffineArrangement.RationalFunctionField (d := d))]
  [originalScalarTower : IsScalarTower ℂ L (AffineArrangement.RationalFunctionField (d := d))]
  [rationalAlgebra : Algebra (RatFunc ℂ) L]
  [rationalFinite : FiniteDimensional (RatFunc ℂ) L]
  [rationalScalarTower : IsScalarTower ℂ (RatFunc ℂ) L]
  [rationalSeparable : Algebra.IsSeparable (RatFunc ℂ) L]

namespace CoefficientCurveScalarContext

attribute [local instance] field complexAlgebra originalAlgebra originalScalarTower
attribute [local instance] rationalAlgebra rationalFinite rationalScalarTower rationalSeparable

end CoefficientCurveScalarContext

attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

/-- Construct the scalar context from the actual extracted coefficient
field, actual inclusion, and genuine finite-extension theorem. -/
def actualCoefficientCurveScalarContext
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) : CoefficientCurveScalarContext d := by
  letI : Module ℂ (AffineArrangement.RationalFunctionField (d := d)) :=
    projectivePolynomialOriginalFieldModule ℂ (Fin d)
  letI : IsScalarTower ℂ ℂ (AffineArrangement.RationalFunctionField (d := d)) :=
    projectivePolynomialOriginalField_selfScalarTower ℂ (Fin d)
  let L : Type := curveCoefficientField ℂ h a b
  letI : Field L := IntermediateField.toField (curveCoefficientField ℂ h a b)
  let cLAlgebra : Algebra ℂ L :=
    inferInstanceAs (Algebra ℂ (curveCoefficientField ℂ h a b))
  letI : Algebra ℂ L := cLAlgebra
  let lFAlgebra : Algebra L (AffineArrangement.RationalFunctionField (d := d)) :=
    IntermediateField.toAlgebra (curveCoefficientField ℂ h a b)
  letI : Algebra L (AffineArrangement.RationalFunctionField (d := d)) := lFAlgebra
  letI : IsScalarTower ℂ L (AffineArrangement.RationalFunctionField (d := d)) := by
    constructor
    intro c l x
    change ((algebraMap ℂ L c : L) : AffineArrangement.RationalFunctionField (d := d)) *
        (l : AffineArrangement.RationalFunctionField (d := d)) * x =
      algebraMap ℂ (AffineArrangement.RationalFunctionField (d := d)) c *
        ((l : AffineArrangement.RationalFunctionField (d := d)) * x)
    have hc : ((algebraMap ℂ L c : L) : AffineArrangement.RationalFunctionField (d := d)) =
        algebraMap ℂ (AffineArrangement.RationalFunctionField (d := d)) c := rfl
    rw [hc, mul_assoc]
  let g : RatFunc ℂ →ₐ[ℂ] L := curveCoefficientRatFuncMap ℂ h a b hh
  letI : Algebra (RatFunc ℂ) L := g.toRingHom.toAlgebra
  letI : Module (RatFunc ℂ) L :=
    @Algebra.toModule (RatFunc ℂ) L
      (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring L))
      g.toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc ℂ) L :=
    curveCoefficientRatFuncMap_finite ℂ h a b hh hfinite
  letI : IsScalarTower ℂ (RatFunc ℂ) L := nativeRatFuncAlgHom_scalarTower g
  letI : Algebra.IsSeparable (RatFunc ℂ) L := inferInstance
  exact
    { L := L
      field := inferInstance
      complexAlgebra := cLAlgebra
      originalAlgebra := lFAlgebra
      originalScalarTower := by
        constructor
        intro c l x
        change ((algebraMap ℂ L c : L) : AffineArrangement.RationalFunctionField (d := d)) *
            (l : AffineArrangement.RationalFunctionField (d := d)) * x =
          algebraMap ℂ (AffineArrangement.RationalFunctionField (d := d)) c *
            ((l : AffineArrangement.RationalFunctionField (d := d)) * x)
        have hc : ((algebraMap ℂ L c : L) : AffineArrangement.RationalFunctionField (d := d)) =
            algebraMap ℂ (AffineArrangement.RationalFunctionField (d := d)) c := rfl
        rw [hc, mul_assoc]
      rationalAlgebra := g.toRingHom.toAlgebra
      rationalFinite := inferInstance
      rationalScalarTower := inferInstance
      rationalSeparable := inferInstance }

end ChenRanks
