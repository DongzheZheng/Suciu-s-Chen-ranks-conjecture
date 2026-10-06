import ChenRanks.ActualNormalizationMixedDescent
import ChenRanks.ActualLogarithmicMaximality

/-!
# Mixed coefficient absorption on the actual normalization

This is the final geometric implication in the paper's logarithmic
separation proof. The source is the native normalization of the original
finite-type integral scheme. Every order row and the avoidance open are
constructed by the actual proper-descent theorem. The curve's actual
function-field comparison makes its differential image isotropic.
Maximality is used only inside the actual finite logarithmic image.

The morphism, pullback witnesses and curve-field comparison are object
data of the preceding construction. Neither coefficient absorption nor
order vanishing nor separability of the original quadratic subspace is
a premise. Original arrangements are connected to this statement by the
actual normalized coefficient graph and differential comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ChenRanks

variable {Y : Scheme} [IsIntegral Y] [CompactSpace Y]

/-- Each actual logarithmic coefficient in the actual mixed relation is
absorbed by maximality inside the original logarithmic image. -/
theorem actualNormalization_mixed_logarithmic_coefficients_mem_maximal_subspace
    (Z : Scheme) [IsIntegral Z]
    (σZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType σZ]
    (σY : Y ⟶ Spec (.of ℂ))
    (f : actualFiniteTypeNormalization Z ⟶ Y) [IsDominant f] [IsProper f]
    (hstructure : f ≫ σY = actualNormalizationScalarMorphism Z σZ)
    (L : Type) [Field L] [Algebra ℂ L] [Algebra (RatFunc ℂ) L]
    [IsScalarTower ℂ (RatFunc ℂ) L] [Algebra.IsSeparable (RatFunc ℂ) L]
    {j : Type*} [Fintype j] :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra ℂ (actualFiniteTypeNormalization Z).functionField :=
      structureFunctionFieldAlgebra (actualNormalizationScalarMorphism Z σZ)
    letI : Algebra Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower ℂ Y.functionField (actualFiniteTypeNormalization Z).functionField :=
      functionFieldScalarTower_of_structure_square
        (actualNormalizationScalarMorphism Z σZ) σY f hstructure
    ∀ (_eL : L ≃ₐ[ℂ] Y.functionField)
      (F : j → (actualFiniteTypeNormalization Z).functionFieldˣ)
      (P : Submodule ℂ Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])
      [FiniteDimensional ℂ P],
      IsMaximalRationallyIsotropicIn
        (LinearMap.range (relativeLogCombination (L := ℂ) F)) P →
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄ℂ],
        KaehlerDifferential.map ℂ ℂ Y.functionField
          (actualFiniteTypeNormalization Z).functionField η =
          (ω : Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])) →
      ∀ (β : Fin (Module.finrank ℂ P) → j → ℂ),
      (∑ i, ∑ a, algebraMap ℂ (actualFiniteTypeNormalization Z).functionField (β i a) •
        exteriorWedge (k := (actualFiniteTypeNormalization Z).functionField)
          (logarithmicDifferential ℂ (actualFiniteTypeNormalization Z).functionField (F a))
          (Module.finBasis ℂ P i :
            Ω[(actualFiniteTypeNormalization Z).functionField⁄ℂ])) = 0 →
      ∀ i, relativeLogCombination (L := ℂ) F (β i) ∈ P := by
  let X := actualFiniteTypeNormalization Z
  let σX := actualNormalizationScalarMorphism Z σZ
  letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro eL F P _ hP hpull β hrelation i
  have hi := actualNormalization_mixed_relation_logarithmic_coefficients_mem_curve_range
    Z σZ σY f hstructure P hpull F β hrelation i
  exact mem_maximal_rational_isotropic_of_actual_curve_image eL
    (LinearMap.range (relativeLogCombination (L := ℂ) F)) P hP hpull
    (relativeLogCombination (L := ℂ) F (β i)) ⟨β i, rfl⟩ hi

end ChenRanks
