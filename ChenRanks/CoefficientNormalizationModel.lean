import ChenRanks.CoefficientCurveScalarContext
import ChenRanks.ArrangementNormalizationPullbackSeparation

/-!
# A genuine coefficient-model bundle and its separation consequence

The bundle records actual schemes, native morphisms, their proved
properties, and the actual differential pullback property. It contains
no separation conclusion. A companion construction supplies this bundle
from the original coefficient field; its existence is not an input of
the final arrangement theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local instance] CoefficientCurveScalarContext.field
attribute [local instance] CoefficientCurveScalarContext.complexAlgebra
attribute [local instance] CoefficientCurveScalarContext.originalAlgebra
attribute [local instance] CoefficientCurveScalarContext.originalScalarTower
attribute [local instance] CoefficientCurveScalarContext.rationalAlgebra
attribute [local instance] CoefficientCurveScalarContext.rationalFinite
attribute [local instance] CoefficientCurveScalarContext.rationalScalarTower
attribute [local instance] CoefficientCurveScalarContext.rationalSeparable

/-- Data of an actual normal proper coefficient model. All fields are
filled by the actual construction, rather than required of an assumed
model in the final theorem. -/
structure CoefficientNormalizationModel (d : ℕ) (S : CoefficientCurveScalarContext d) where
  Y : Scheme
  [integralY : IsIntegral Y]
  [compactY : CompactSpace Y]
  Z : Scheme
  [integralZ : IsIntegral Z]
  σZ : Z ⟶ Spec (.of ℂ)
  [finiteTypeZ : LocallyOfFiniteType σZ]
  σY : Y ⟶ Spec (.of ℂ)
  f : actualFiniteTypeNormalization Z ⟶ Y
  [dominantF : IsDominant f]
  [properF : IsProper f]
  structure_eq : f ≫ σY = actualNormalizationScalarMorphism Z σZ
  originalFieldEquiv :
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    AffineArrangement.RationalFunctionField (d := d) ≃ₐ[ℂ]
      (actualFiniteTypeNormalization Z).functionField
  curveFieldEquiv :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    S.L ≃ₐ[ℂ] Y.functionField
  pullbackProperty :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    letI : Algebra Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower ℂ Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      functionFieldScalarTower_of_structure_square
        (actualNormalizationScalarMorphism Z σZ) σY f structure_eq
    actualCoefficientModelPullbackProperty S.L Y.functionField originalFieldEquiv.symm

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The proved native-model separation theorem consumes a genuinely
constructed bundle. This generic implication by itself does not assert
that the bundle exists for a particular arrangement. -/
theorem rationalQuadraticKernel_separated_of_coefficient_model
    (S : CoefficientCurveScalarContext d) (M : CoefficientNormalizationModel d S)
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P)
    (hpull : ∀ ω : A.realizedLogarithmicSubspace P, ∃ η : Ω[S.L⁄ℂ],
      KaehlerDifferential.map ℂ ℂ S.L (RationalFunctionField (d := d)) η =
        (ω : Ω[RationalFunctionField (d := d)⁄ℂ])) :
    mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P := by
  letI : IsIntegral M.Y := M.integralY
  letI : CompactSpace M.Y := M.compactY
  letI : IsIntegral M.Z := M.integralZ
  letI : LocallyOfFiniteType M.σZ := M.finiteTypeZ
  letI : IsDominant M.f := M.dominantF
  letI : IsProper M.f := M.properF
  letI : Algebra ℂ M.Y.functionField := structureFunctionFieldAlgebra M.σY
  letI : Algebra ℂ (actualFiniteTypeNormalization M.Z).functionField :=
    structureFunctionFieldAlgebra (actualNormalizationScalarMorphism M.Z M.σZ)
  letI : Algebra M.Y.functionField (actualFiniteTypeNormalization M.Z).functionField :=
    (dominantFunctionFieldMap M.f).hom.toAlgebra
  letI : IsScalarTower ℂ M.Y.functionField (actualFiniteTypeNormalization M.Z).functionField :=
    functionFieldScalarTower_of_structure_square
      (actualNormalizationScalarMorphism M.Z M.σZ) M.σY M.f M.structure_eq
  exact A.rationalQuadraticKernel_separated_on_actual_normalization_of_curve_pullbacks
    M.Z M.σZ M.σY M.f M.structure_eq S.L
    M.originalFieldEquiv M.curveFieldEquiv P hP M.pullbackProperty hpull

end AffineArrangement

end ChenRanks
