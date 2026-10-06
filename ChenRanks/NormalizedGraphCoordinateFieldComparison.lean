import ChenRanks.RationalGraphOriginalFieldComparison
import ChenRanks.NormalizationFieldTransport

/-! The actual generic coordinate inclusion determines the native
projection of the actual normalized graph. Normalization cancellation
and fraction-ring extensionality prove the complete field identity.
The graph and normalization are the genuine native constructions;
neither a chosen model nor a function-field projection identity is an
input. The coordinate formula for the genuine generic arrow is the
structural input supplied by the actual coefficient construction. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

universe u

variable {X S : Scheme.{u}} [IsIntegral X]
  (B L F : Type u) [CommRing B] [IsDomain B] [Field L] [Field F]
  [Algebra B L] [IsFractionRing B L]
  (σX : X ⟶ S) (σB : Spec (.of B) ⟶ S) [LocallyOfFiniteType σB]
  (φ : {r : X.RationalMap (Spec (.of B)) // r.compHom σB = σX.toRationalMap})
  [IsDominant (rationalGraphGenericArrow σX σB φ)]

/-- The normalization cancels inside the actual native curve
projection, and the actual generic coordinate map fixes the full
original coefficient inclusion. -/
theorem normalizedGraphCoordinateFieldComparison
    (eX : X.functionField ≃+* F)
    (eB : (Spec (.of B)).functionField ≃ₐ[B] L)
    (i : L →+* F)
    (hφ : rationalGraphGenericArrow σX σB φ =
      Spec.map (CommRingCat.ofHom
        (eX.symm.toRingHom.comp (i.comp (algebraMap B L))))) :
    let Z := rationalGraphImage σX σB φ
    let π := rationalGraphProjectionCurve σX σB φ
    letI : IsDominant π := rationalGraphProjectionCurve_isDominant σX σB φ
    eX.toRingHom.comp
        ((rationalGraphImageFunctionFieldEquiv σX σB φ).toRingHom.comp
          ((actualNormalizationFunctionFieldEquiv Z).toRingHom.comp
            (dominantFunctionFieldMap (actualFiniteTypeNormalizationMap Z ≫ π)).hom)) =
      i.comp eB.toRingHom := by
  let Z := rationalGraphImage σX σB φ
  let π := rationalGraphProjectionCurve σX σB φ
  letI : IsDominant π := rationalGraphProjectionCurve_isDominant σX σB φ
  dsimp only
  rw [actualNormalizationFunctionFieldEquiv_comp_morphism]
  exact rationalGraphOriginalFieldComparison B L F σX σB φ eX eB i hφ

end ChenRanks
