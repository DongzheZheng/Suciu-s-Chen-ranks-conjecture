import ChenRanks.ScalarContextCoefficientRationalMap
import ChenRanks.NormalizedRationalGraph

/-! Native dominance of the actual coefficient graph under its actual
constructed scalar context. The field inclusion and the generic-arrow
comparison are already proved for the original coefficients; no
dominance or nonconstant-map premise is added. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The actual graph's actual generic curve arrow is dominant, by the
already proved original coefficient-field inclusion. -/
theorem scalarContextCoefficientGraphGenericArrow_isDominant
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    let S := actualCoefficientCurveScalarContext h a b hh hfinite
    letI : Field S.L := S.field
    letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
    letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
    letI : Module (RatFunc ℂ) S.L :=
      @Algebra.toModule (RatFunc ℂ) S.L
        (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
        S.rationalAlgebra
    letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
    let σX := projectivePolynomialScalarMorphism ℂ (Option (Fin d))
    let σC := curveAffineNormalizationScalarMorphism ℂ S.L
    let φ := scalarContextCoefficientRationalMap h a b hh hfinite
    letI : LocallyOfFiniteType σC :=
      curveAffineNormalizationScalarMorphism_locallyOfFiniteType ℂ S.L
    IsDominant (rationalGraphGenericArrow σX σC φ) := by
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  letI : Field S.L := S.field
  letI : Algebra (RatFunc ℂ) S.L := S.rationalAlgebra
  letI : SMul (RatFunc ℂ) S.L := S.rationalAlgebra.toSMul
  letI : Module (RatFunc ℂ) S.L :=
    @Algebra.toModule (RatFunc ℂ) S.L
      (inferInstanceAs (CommSemiring (RatFunc ℂ))) (inferInstanceAs (Semiring S.L))
      S.rationalAlgebra
  letI : FiniteDimensional (RatFunc ℂ) S.L := S.rationalFinite
  let σX := projectivePolynomialScalarMorphism ℂ (Option (Fin d))
  let σC := curveAffineNormalizationScalarMorphism ℂ S.L
  let φ := scalarContextCoefficientRationalMap h a b hh hfinite
  letI : LocallyOfFiniteType σC :=
    curveAffineNormalizationScalarMorphism_locallyOfFiniteType ℂ S.L
  exact actualMorphismDominance_of_equality
    (rationalGraphGenericArrow σX σC φ)
    (projectiveCoefficientGenericMorphism ℂ (Fin d) h a b hh)
    (projectiveCoefficientRationalMap_genericArrow ℂ (Fin d) h a b hh hfinite)
    (projectiveCoefficientGenericMorphism_isDominant ℂ (Fin d) h a b hh hfinite)

end ChenRanks
