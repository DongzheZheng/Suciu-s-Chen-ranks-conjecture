import ChenRanks.ActualCoefficientModelPullbackStatements
import ChenRanks.CoefficientModelFieldSquare

/-!
# Actual original curve pullbacks on the actual normalized coefficient model

The source and target are the native finite normalization of the actual
coefficient graph and the actual affine normalization of the original
coefficient field. Their function-field comparisons are the already
constructed comparisons over the original scalar field. The actual native
projection equality proves the original field square, and native differential
naturality carries every original pullback witness to the actual model.

Only the original transcendental coefficient and its original finite curve
extension are inputs of the model construction. No chosen model, function-field
comparison, projection compatibility, residue detector or model pullback is
supplied as a premise.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

section PolynomialModel

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The actual normalized coefficient model's two constructed inverse
comparisons commute with the original coefficient-subfield inclusion. -/
theorem normalizedProjectiveCoefficient_original_field_square
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    normalizedProjectiveCoefficientOriginalFieldSquareStatement k ι h a b hh hfinite := by
  unfold normalizedProjectiveCoefficientOriginalFieldSquareStatement
  letI : Module k (projectivePolynomialOriginalFunctionField k ι) :=
    projectivePolynomialOriginalFieldModule k ι
  letI : IsScalarTower k k (projectivePolynomialOriginalFunctionField k ι) :=
    projectivePolynomialOriginalField_selfScalarTower k ι
  let L : Type u := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  let N : Scheme.{u} := normalizedRationalGraph σX σC φ
  let f : N ⟶ curveAffineNormalization k L := normalizedRationalGraphToCurve σX σC φ
  letI : Algebra k (curveAffineNormalization k L).functionField :=
    structureFunctionFieldAlgebra σC
  letI : Algebra k N.functionField :=
    structureFunctionFieldAlgebra (normalizedRationalGraphScalarMorphism σX σC φ)
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : Algebra (curveAffineNormalization k L).functionField N.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  dsimp only
  intro x
  exact inverseComparisons_original_field_square
    (normalizedProjectiveCoefficientFunctionFieldAlgEquiv k ι h a b hh hfinite)
    (curveCoefficientNormalizationFunctionFieldAlgEquiv k h a b hh hfinite)
    (dominantFunctionFieldMap f).hom
    (normalizedProjectiveCoefficientCurveFieldMap_eq_original_inclusion
      k ι h a b hh hfinite) x

/-- Every original differential pullback to the coefficient field gives
the corresponding pullback to the actual curve on the actual normalized
model. The native field square is proved by the preceding factory. -/
theorem normalizedProjectiveCoefficient_original_subspace_pullbacks
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) :
    normalizedProjectiveCoefficientOriginalSubspacePullbacksStatement k ι h a b hh hfinite := by
  unfold normalizedProjectiveCoefficientOriginalSubspacePullbacksStatement
  letI : Module k (projectivePolynomialOriginalFunctionField k ι) :=
    projectivePolynomialOriginalFieldModule k ι
  letI : IsScalarTower k k (projectivePolynomialOriginalFunctionField k ι) :=
    projectivePolynomialOriginalField_selfScalarTower k ι
  let L : Type u := curveCoefficientField k h a b
  letI : Algebra (RatFunc k) L :=
    (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : Module (RatFunc k) L :=
    @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc k) L :=
    curveCoefficientRatFuncMap_finite k h a b hh hfinite
  let σX := projectivePolynomialScalarMorphism k (Option ι)
  let σC := curveAffineNormalizationScalarMorphism k L
  let φ := projectiveCoefficientRationalMap k ι h a b hh hfinite
  let N : Scheme.{u} := normalizedRationalGraph σX σC φ
  let σN : N ⟶ Spec (.of k) := normalizedRationalGraphScalarMorphism σX σC φ
  let f : N ⟶ curveAffineNormalization k L := normalizedRationalGraphToCurve σX σC φ
  letI : Algebra k (curveAffineNormalization k L).functionField :=
    structureFunctionFieldAlgebra σC
  letI : Algebra k N.functionField := structureFunctionFieldAlgebra σN
  letI : IsDominant (rationalGraphGenericArrow σX σC φ) :=
    actualMorphismDominance_of_equality
      (rationalGraphGenericArrow σX σC φ)
      (projectiveCoefficientGenericMorphism k ι h a b hh)
      (projectiveCoefficientRationalMap_genericArrow k ι h a b hh hfinite)
      (projectiveCoefficientGenericMorphism_isDominant k ι h a b hh hfinite)
  letI : Algebra (curveAffineNormalization k L).functionField N.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k (curveAffineNormalization k L).functionField N.functionField :=
    functionFieldScalarTower_of_structure_square σN σC f
      (normalizedRationalGraphToCurve_structure σX σC φ)
  dsimp only
  exact actualCoefficientModelPullbackProperty_of_identity
    L (curveAffineNormalization k L).functionField
    (normalizedProjectiveCoefficientFunctionFieldAlgEquiv k ι h a b hh hfinite)
    (curveCoefficientNormalizationFunctionFieldAlgEquiv k h a b hh hfinite)
    (normalizedProjectiveCoefficientCurveFieldMap_eq_original_inclusion
      k ι h a b hh hfinite)


end PolynomialModel

end

end ChenRanks
