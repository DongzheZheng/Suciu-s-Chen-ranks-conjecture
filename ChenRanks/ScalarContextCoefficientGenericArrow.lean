import ChenRanks.ProjectiveCoefficientNativeCoordinates
import ChenRanks.CoefficientCurveScalarContextNative
import ChenRanks.ScalarContextCoefficientProjection
import ChenRanks.ScalarContextCoefficientFieldComparisons

/-! The actual generic coordinate arrow of the constructed coefficient
curve, with the same native scalar context as the normalized model.
Only this coordinate formula is cached here. Neither a model nor a
projection compatibility condition is supplied as a hypothesis. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

attribute [local instance] projectivePolynomialOriginalFieldAlgebra
attribute [local instance] projectivePolynomialOriginalFieldSMul
attribute [local instance] projectivePolynomialOriginalFieldModule
attribute [local irreducible] curveCoefficientField curveCoefficientRatFuncMap
attribute [local irreducible] projectiveCoefficientRationalMap

/-- The native rational-map factory recovers its original generic
coefficient arrow. This identity uses only the scalar dictionaries
actually needed to construct that map. -/
theorem scalarContextCoefficientGenericArrow_eq_original
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
    rationalGraphGenericArrow σX σC φ =
      projectiveCoefficientGenericMorphism ℂ (Fin d) h a b hh := by
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
  exact projectiveCoefficientRationalMap_genericArrow ℂ (Fin d) h a b hh hfinite

/-- The exact coordinate identity for the actual generic arrow, before
normalization or differential transport. -/
def scalarContextCoefficientGenericArrowStatement
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) : Prop :=
  let S := actualCoefficientCurveScalarContext h a b hh hfinite
  letI : Field S.L := S.field
  letI : Algebra S.L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra
  letI : SMul S.L (AffineArrangement.RationalFunctionField (d := d)) := S.originalAlgebra.toSMul
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
  let B : Type := curveAffineNormalizationRing ℂ S.L
  letI : CommRing B := curveAffineNormalizationRing_commRing ℂ S.L
  letI : Algebra B S.L := curveAffineNormalizationRing_fieldAlgebra ℂ S.L
  letI : Algebra ℂ (projectivePolynomialAmbient ℂ (Option (Fin d))).functionField :=
    structureFunctionFieldAlgebra σX
  let eX : (projectivePolynomialAmbient ℂ (Option (Fin d))).functionField ≃+*
      AffineArrangement.RationalFunctionField (d := d) :=
    (projectivePolynomialFunctionFieldAlgEquiv ℂ (Fin d)).toRingEquiv
  let i : S.L →+* AffineArrangement.RationalFunctionField (d := d) :=
    algebraMap S.L (AffineArrangement.RationalFunctionField (d := d))
  rationalGraphGenericArrow σX σC φ =
    Spec.map (CommRingCat.ofHom
      (eX.symm.toRingHom.comp (i.comp (algebraMap B S.L))))

-- A bounded elaboration allowance only for this proved native assembly.
set_option maxHeartbeats 400000 in
/-- The original coefficient construction proves this actual arrow
formula. The input is only the original coefficient data and its proved
transcendence and finite extension properties. -/
theorem scalarContextCoefficientGenericArrow_eq_coordinates
    {d : ℕ} {τ : Type*}
    (h a : AffineArrangement.RationalFunctionField (d := d))
    (b : τ → AffineArrangement.RationalFunctionField (d := d))
    (hh : Transcendental ℂ h)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {h})
      (curveCoefficientField ℂ h a b)) :
    scalarContextCoefficientGenericArrowStatement h a b hh hfinite := by
  trace "native coefficient arrow: proof started"
  have hArrow := scalarContextCoefficientGenericArrow_eq_original h a b hh hfinite
  trace "native coefficient arrow: genuine original arrow recovered"
  unfold scalarContextCoefficientGenericArrowStatement
  dsimp only
  simp only [actualCoefficientCurveScalarContext_native_field,
    actualCoefficientCurveScalarContext_native_rationalAlgebra,
    actualCoefficientCurveScalarContext_native_originalAlgebra] at hArrow ⊢
  trace "native coefficient arrow: actual dictionaries normalized"
  apply hArrow.trans
  trace "native coefficient arrow: actual morphism middle type matched"
  change Spec.map (CommRingCat.ofHom
    (projectiveCoefficientGenericRingHom ℂ (Fin d) h a b hh)) = _
  apply congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ))
  apply RingHom.ext
  intro x
  exact projectiveCoefficientGenericRingHom_apply_native h a b hh x

end ChenRanks
