import ChenRanks.NormalizedProjectiveCoefficientFieldObjects

/-!
# The exact actual normalized coefficient inclusion statement

This proposition definition stores the concrete mathematical formula and
its actual metadata. It does not assume or prove native projection
compatibility; that equality is the conclusion of the separate proof.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable (k ι : Type u) [Field k] [CharZero k] [Finite ι] {τ : Type*}

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] projectiveCoefficientRationalMap
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

def normalizedProjectiveCoefficientCurveFieldInclusionStatement
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
    normalizedProjectiveCoefficientCurveFieldMap k ι h a b hh hfinite =
      (algebraMap L (projectivePolynomialOriginalFunctionField k ι)).comp
        (curveAffineNormalizationFunctionFieldAlgEquiv k L).toRingHom

end

end ChenRanks
