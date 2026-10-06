import ChenRanks.NormalizedLogarithmicMixedSeparation
import ChenRanks.OriginalBasisToModelNativeBasis

/-!
# Returning actual proper-model separation to the original arrangement

The mixed vector belongs to the original generator exterior square.
The native model basis is pulled back to that original space. The actual
proper-normalization descent proves coefficient absorption on the model,
and actual degree-one injectivity reflects it back to the original space.
Thus the separation equality is the conclusion, not a model-data premise.

The actual morphism, field comparisons and pullback witnesses are the
geometric data supplied by the actual coefficient-model factory. This
intermediate theorem does not yet identify the rational quadratic kernel
with the actual topological cup-product kernel.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
  {Y : Scheme} [IsIntegral Y] [CompactSpace Y]

/-- Actual relatively proper curve geometry proves the original exterior
separation equality, using the original genuine quadratic relation map. -/
theorem rationalQuadraticKernel_separated_on_actual_normalization
    (Z : Scheme) [IsIntegral Z]
    (σZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType σZ]
    (σY : Y ⟶ Spec (.of ℂ))
    (f : actualFiniteTypeNormalization Z ⟶ Y) [IsDominant f] [IsProper f]
    (hstructure : f ≫ σY = actualNormalizationScalarMorphism Z σZ)
    (L : Type) [Field L] [Algebra ℂ L] [Algebra (RatFunc ℂ) L]
    [IsScalarTower ℂ (RatFunc ℂ) L] [Algebra.IsSeparable (RatFunc ℂ) L] :
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
      (∀ ω : A.modelLogarithmicSubspace eF P, ∃ η : Ω[Y.functionField⁄ℂ],
        KaehlerDifferential.map ℂ ℂ Y.functionField
          (actualFiniteTypeNormalization Z).functionField η =
          (ω : Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])) →
      mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P := by
  classical
  let X := actualFiniteTypeNormalization Z
  let σX := actualNormalizationScalarMorphism Z σZ
  letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro eF eL P hP hpull
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hc, hmodel⟩ := A.original_mixed_relation_has_model_native_basis_representation
      eF P z hz.1 hz.2
    have hmem := actualNormalization_mixed_logarithmic_coefficients_mem_maximal_subspace
      Z σZ σY f hstructure L eL (A.modelEquationUnit eF)
      (A.modelLogarithmicSubspace eF P)
      (A.modelLogarithmicSubspace_maximal_in_model_logCombination_range eF P hP)
      hpull c hmodel
    apply A.original_mixed_representation_mem_pure_of_actual_model_coefficients eF P z c hc
    intro i
    rw [A.modelLogarithmicRealization_eq_logCombination eF (c i)]
    exact hmem i
  · exact le_inf (pureExterior_le_mixed P)
      (pureExterior_le_ker A.quadraticLogarithmicRealization P hP.1)

end ChenRanks.AffineArrangement
