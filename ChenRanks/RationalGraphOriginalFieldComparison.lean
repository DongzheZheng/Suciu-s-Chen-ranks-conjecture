import ChenRanks.RationalGraphFieldMapCoordinates

/-!
# The complete original field inclusion from the actual generic arrow

The actual graph projection is first computed on actual affine coordinates.
Fraction-ring extensionality then identifies its complete field map after
transport through the actual source comparison.  The generic arrow is the
Spec map of the coordinate inclusion transported through that comparison.
Only this actual coordinate construction is an input; compatibility of the
native curve projection is a conclusion.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} [IsIntegral X]
  (B L F : Type u) [CommRing B] [IsDomain B] [Field L] [Field F]
  [Algebra B L] [IsFractionRing B L]
  (σX : X ⟶ S) (σB : Spec (.of B) ⟶ S) [LocallyOfFiniteType σB]
  (φ : {r : X.RationalMap (Spec (.of B)) // r.compHom σB = σX.toRationalMap})
  [IsDominant (rationalGraphGenericArrow σX σB φ)]

/-- The actual generic coordinate inclusion determines the complete
native curve-projection map, not only its values on coordinates. -/
theorem rationalGraphOriginalFieldComparison
    (eX : X.functionField ≃+* F)
    (eB : (Spec (.of B)).functionField ≃ₐ[B] L)
    (i : L →+* F)
    (hφ : rationalGraphGenericArrow σX σB φ =
      Spec.map (CommRingCat.ofHom
        (eX.symm.toRingHom.comp (i.comp (algebraMap B L))))) :
    letI : IsDominant (rationalGraphProjectionCurve σX σB φ) :=
      rationalGraphProjectionCurve_isDominant σX σB φ
    eX.toRingHom.comp
        ((rationalGraphImageFunctionFieldEquiv σX σB φ).toRingHom.comp
          (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σB φ)).hom) =
      i.comp eB.toRingHom := by
  letI : IsDominant (rationalGraphProjectionCurve σX σB φ) :=
    rationalGraphProjectionCurve_isDominant σX σB φ
  let ψ : B →+* X.functionField :=
    eX.symm.toRingHom.comp (i.comp (algebraMap B L))
  have hψ : Function.Injective ψ :=
    eX.symm.injective.comp (i.injective.comp (IsFractionRing.injective B L))
  apply IsFractionRing.ringHom_ext
    (A := B) (K := (Spec (.of B)).functionField) (L := F)
  intro b
  change eX (rationalGraphImageFunctionFieldEquiv σX σB φ
      (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σB φ)
        (algebraMap B (Spec (.of B)).functionField b))) =
    i (eB (algebraMap B (Spec (.of B)).functionField b))
  rw [rationalGraphImageFunctionFieldEquiv_curve_algebraMap
    B σX σB φ ψ hψ hφ b, eB.commutes]
  change eX (eX.symm (i (algebraMap B L b))) = i (algebraMap B L b)
  exact eX.apply_symm_apply _

end

end ChenRanks
