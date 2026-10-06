import ChenRanks.ArrangementSeparationOnActualNormalization
import ChenRanks.CoefficientModelPullbackProperty

/-!
# Native normalization separation from the proved differential field square

This generic adapter keeps the native scheme scalar actions and the
literal differential pullback predicate together. Its concrete use fills
the predicate by the proved actual coefficient-model field square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
  {Y : Scheme} [IsIntegral Y] [CompactSpace Y]

/-- A proved native field-square pullback property supplies the actual
model pullbacks required by the proper-normalization separation theorem. -/
theorem rationalQuadraticKernel_separated_on_actual_normalization_of_curve_pullbacks
    (Z : Scheme) [IsIntegral Z]
    (σZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType σZ]
    (σY : Y ⟶ Spec (.of ℂ))
    (f : actualFiniteTypeNormalization Z ⟶ Y) [IsDominant f] [IsProper f]
    (hstructure : f ≫ σY = actualNormalizationScalarMorphism Z σZ)
    (L : Type) [Field L] [Algebra ℂ L] [Algebra (RatFunc ℂ) L]
    [IsScalarTower ℂ (RatFunc ℂ) L] [Algebra.IsSeparable (RatFunc ℂ) L]
    [Algebra L (RationalFunctionField (d := d))]
    [IsScalarTower ℂ L (RationalFunctionField (d := d))] :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    letI : Algebra Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower ℂ Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      functionFieldScalarTower_of_structure_square
        (actualNormalizationScalarMorphism Z σZ) σY f hstructure
    ∀ (eF : RationalFunctionField (d := d) ≃ₐ[ℂ]
        (actualFiniteTypeNormalization Z).functionField)
      (_eL : L ≃ₐ[ℂ] Y.functionField) (P : Submodule ℂ (ι → ℂ)),
      IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P →
      actualCoefficientModelPullbackProperty L Y.functionField eF.symm →
      (∀ ω : A.realizedLogarithmicSubspace P, ∃ η : Ω[L⁄ℂ],
        KaehlerDifferential.map ℂ ℂ L (RationalFunctionField (d := d)) η =
          (ω : Ω[RationalFunctionField (d := d)⁄ℂ])) →
      mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P := by
  let X := actualFiniteTypeNormalization Z
  let σX := actualNormalizationScalarMorphism Z σZ
  letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro eF eL P hP hproperty hpull
  apply A.rationalQuadraticKernel_separated_on_actual_normalization
    Z σZ σY f hstructure L eF eL P hP
  rw [A.modelLogarithmicSubspace_eq_map_realized eF P]
  exact hproperty (A.realizedLogarithmicSubspace P) hpull

end ChenRanks.AffineArrangement
