import ChenRanks.ActualCoefficientModelPullbacks
import ChenRanks.ActualLogarithmicFieldTransport
import ChenRanks.ArrangementIsotropicRealization

/-!
# Exact original arrangement curve statements

The original curve pullback proposition is written once for the actual
coefficient subfield and the actual logarithmic image. These are complete
proposition definitions, not hypotheses about a selected geometric model.
They retain the original affine arrangement's scalar action.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] quadraticLogarithmicRealization logarithmicRealization

variable {d : ℕ} {ι τ : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The full original differential pullback statement for the actual
coefficient field of the original rational functions. -/
def arrangementOriginalCurvePullbackStatement
    (h a : RationalFunctionField (d := d))
    (b : τ → RationalFunctionField (d := d)) (P : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ ω : A.realizedLogarithmicSubspace P,
    ∃ η : Ω[(curveCoefficientField ℂ h a b)⁄ℂ],
      KaehlerDifferential.map ℂ ℂ (curveCoefficientField ℂ h a b)
        (RationalFunctionField (d := d)) η =
          (ω : Ω[RationalFunctionField (d := d)⁄ℂ])

/-- The complete original separation implication. The transcendence
and finiteness needed to construct the model are arguments of its proof,
and no model data occur in this proposition. -/
def arrangementOriginalCurveSeparationStatement
    (h a : RationalFunctionField (d := d))
    (b : τ → RationalFunctionField (d := d)) : Prop :=
  ∀ (P : Submodule ℂ (ι → ℂ)),
    IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P →
    A.arrangementOriginalCurvePullbackStatement h a b P →
      mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P

end ChenRanks.AffineArrangement
