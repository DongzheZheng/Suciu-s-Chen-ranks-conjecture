import ChenRanks.ProjectiveCoefficientFieldObjects

/-!
# Exact propositions for the original coefficient inclusion

These definitions cache the concrete actual field-map statements, including
all actual coefficient-field and native coordinate-ring structures. They are
only proposition definitions. Neither statement is assumed or proved by this
file; their actual proofs are the separate native graph comparisons.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap projectiveCoefficientCurveFieldMap

def projectiveCoefficientCurveFieldInclusionStatement
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) : Prop :=
    let L : Type u := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : Module (RatFunc k) L :=
      @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
        (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc k) L :=
      curveCoefficientRatFuncMap_finite k h a b hh hfinite
    projectiveCoefficientCurveFieldMap k ι h a b hh hfinite =
      (algebraMap L (projectivePolynomialOriginalFunctionField k ι)).comp
        (curveAffineNormalizationFunctionFieldAlgEquiv k L).toRingHom

def projectiveCoefficientCurveFieldCoordinatesStatement
    (h a : projectivePolynomialOriginalFunctionField k ι)
    (b : τ → projectivePolynomialOriginalFunctionField k ι)
    (hh : Transcendental k h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin k {h})
      (curveCoefficientField k h a b)) : Prop :=
    let L : Type u := curveCoefficientField k h a b
    letI : Algebra (RatFunc k) L :=
      (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : Module (RatFunc k) L :=
      @Algebra.toModule (RatFunc k) L
        (inferInstanceAs (CommSemiring (RatFunc k))) (inferInstanceAs (Semiring L))
        (curveCoefficientRatFuncMap k h a b hh).toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc k) L :=
      curveCoefficientRatFuncMap_finite k h a b hh hfinite
    ∀ z : curveAffineNormalizationRing k L,
      projectiveCoefficientCurveFieldMap k ι h a b hh hfinite
          (algebraMap (curveAffineNormalizationRing k L)
            (curveAffineNormalization k L).functionField z) =
        algebraMap L (projectivePolynomialOriginalFunctionField k ι)
          (algebraMap (curveAffineNormalizationRing k L) L z)

end

end ChenRanks
