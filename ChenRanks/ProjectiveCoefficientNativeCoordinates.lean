import ChenRanks.ProjectiveCoefficientRationalMap

/-! The original coefficient ring map's actual function-level formula.
This avoids identifying separately reconstructed RingHom dictionaries
or native Spec morphism types before computing their actual values. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialActualFunctionFieldAlgebra
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap

/-- The defining native coordinate map applies the genuine inverse
projective comparison to the actual normalization-ring inclusion. -/
theorem projectiveCoefficientGenericRingHom_apply_native
    {d : ℕ} {τ : Type*}
    (h a : projectivePolynomialOriginalFunctionField ℂ (Fin d))
    (b : τ → projectivePolynomialOriginalFunctionField ℂ (Fin d))
    (hh : Transcendental ℂ h) :
    let L := curveCoefficientField ℂ h a b
    letI : Algebra (RatFunc ℂ) L :=
      (curveCoefficientRatFuncMap ℂ h a b hh).toRingHom.toAlgebra
    ∀ x : curveAffineNormalizationRing ℂ L,
      projectiveCoefficientGenericRingHom ℂ (Fin d) h a b hh x =
        (projectivePolynomialFunctionFieldAlgEquiv ℂ (Fin d)).symm
          ((x.val : L) : projectivePolynomialOriginalFunctionField ℂ (Fin d)) := by
  dsimp only
  intro x
  rfl

end ChenRanks
