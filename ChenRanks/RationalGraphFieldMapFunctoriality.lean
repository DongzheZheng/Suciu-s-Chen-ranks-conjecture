import ChenRanks.RationalGraphFunctionField
import ChenRanks.AffineGenericFieldMap

/-!
# Native functoriality of the actual graph-to-curve field map

The comparison is computed for the genuine native graph of the genuine
rational map.  Its generic-image triangle and native contravariant
function-field composition prove the equality.  There is no coefficient
field, curve-construction choice, or supplied map-compatibility premise
in this bounded generic lemma.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

private theorem nativeGraphFieldMap_congr {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B]
    (f g : A ⟶ B) [IsDominant f] [IsDominant g] (h : f = g) :
    dominantFunctionFieldMap f = dominantFunctionFieldMap g := by
  subst g
  rfl

variable {X C S : Scheme.{u}} [IsIntegral X] [IsIntegral C]
  (σX : X ⟶ S) (σC : C ⟶ S) [LocallyOfFiniteType σC]
  (φ : {r : X.RationalMap C // r.compHom σC = σX.toRationalMap})
  [IsDominant (rationalGraphGenericArrow σX σC φ)]

/-- The actual graph field comparison transports its native curve
projection map to the native actual generic-arrow field map. -/
theorem rationalGraphImageFunctionFieldEquiv_comp_curve :
    letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
      rationalGraphProjectionCurve_isDominant σX σC φ
    (rationalGraphImageFunctionFieldEquiv σX σC φ).toRingHom.comp
        (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σC φ)).hom =
      (affineCoordinateFunctionFieldEquiv
        (X.functionField : Type u) (X.functionField : Type u)).toRingHom.comp
          (dominantFunctionFieldMap (rationalGraphGenericArrow σX σC φ)).hom := by
  letI : IsDominant (rationalGraphProjectionCurve σX σC φ) :=
    rationalGraphProjectionCurve_isDominant σX σC φ
  ext x
  have hc := dominantFunctionFieldMap_comp
    (rationalGraphToImage σX σC φ) (rationalGraphProjectionCurve σX σC φ)
  have hc' := hc.trans (nativeGraphFieldMap_congr
    (rationalGraphToImage σX σC φ ≫ rationalGraphProjectionCurve σX σC φ)
    (rationalGraphGenericArrow σX σC φ)
    (rationalGraphToImage_projectionCurve σX σC φ))
  have hx := congrArg
    (fun f : C.functionField ⟶ (Spec X.functionField).functionField => f x) hc'
  change dominantFunctionFieldMap (rationalGraphToImage σX σC φ)
      (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σC φ) x) =
    dominantFunctionFieldMap (rationalGraphGenericArrow σX σC φ) x at hx
  change (affineCoordinateFunctionFieldEquiv
      (X.functionField : Type u) (X.functionField : Type u))
      (dominantFunctionFieldMap (rationalGraphToImage σX σC φ)
        (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σC φ) x)) = _
  rw [hx]
  rfl

end

end ChenRanks
