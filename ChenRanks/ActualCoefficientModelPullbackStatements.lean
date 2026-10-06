import ChenRanks.NormalizedProjectiveCoefficientFieldMap
import ChenRanks.CoefficientModelPullbackProperty
import ChenRanks.ProjectiveOriginalScalarActions

/-!
# Exact statements for the actual coefficient-model pullbacks

These definitions cache the complete propositions for the actual graph,
normalization, native field maps and original scalar actions. They are
literal statements, not assumptions or proof certificates. Their proofs
are provided in `ActualCoefficientModelPullbacks`.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] projectiveCoefficientRationalMap
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

def normalizedProjectiveCoefficientOriginalFieldSquareStatement
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) : Prop :=
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
    let N := normalizedRationalGraph σX σC φ
    let f := normalizedRationalGraphToCurve σX σC φ
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
    ∀ x : L,
      (normalizedProjectiveCoefficientFunctionFieldAlgEquiv k ι h a b hh hfinite).symm
          (algebraMap L (projectivePolynomialOriginalFunctionField k ι) x) =
        algebraMap (curveAffineNormalization k L).functionField N.functionField
          ((curveCoefficientNormalizationFunctionFieldAlgEquiv k h a b hh hfinite).symm x)

def normalizedProjectiveCoefficientOriginalSubspacePullbacksStatement
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) : Prop :=
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
    let N := normalizedRationalGraph σX σC φ
    let σN := normalizedRationalGraphScalarMorphism σX σC φ
    let f := normalizedRationalGraphToCurve σX σC φ
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
    actualCoefficientModelPullbackProperty L (curveAffineNormalization k L).functionField
      (normalizedProjectiveCoefficientFunctionFieldAlgEquiv k ι h a b hh hfinite)


end ChenRanks
