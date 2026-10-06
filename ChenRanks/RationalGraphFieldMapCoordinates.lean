import ChenRanks.RationalGraphFieldMapFunctoriality
import ChenRanks.StructureFunctionFieldTower

/-!
# Actual graph projection maps on actual affine coordinates

The generic triangle identifies the actual graph's curve projection with
the actual affine generic arrow. The induced function-field map is evaluated
on the original coordinate ring using the native affine comparison. The
structural scalar square also proves scalar compatibility of an actual
composite with an actual base-field equivalence.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

private theorem coordinateFieldMap_congr {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) :
    dominantFunctionFieldMap f = dominantFunctionFieldMap g := by
  subst g
  rfl

section GraphCoordinates

variable {X S : Scheme.{u}} [IsIntegral X]
  (B : Type u) [CommRing B] [IsDomain B]
  (σX : X ⟶ S) (σB : Spec (.of B) ⟶ S) [LocallyOfFiniteType σB]
  (φ : {r : X.RationalMap (Spec (.of B)) // r.compHom σB = σX.toRationalMap})
  [IsDominant (rationalGraphGenericArrow σX σB φ)]

/-- Evaluation on the original affine coordinate ring follows from
the actual generic-arrow equality and actual native field functoriality. -/
theorem rationalGraphImageFunctionFieldEquiv_curve_algebraMap
    (ψ : B →+* X.functionField) (hψ : Function.Injective ψ)
    (hφ : rationalGraphGenericArrow σX σB φ = Spec.map (CommRingCat.ofHom ψ))
    (b : B) :
    letI : IsDominant (rationalGraphProjectionCurve σX σB φ) :=
      rationalGraphProjectionCurve_isDominant σX σB φ
    rationalGraphImageFunctionFieldEquiv σX σB φ
      (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σB φ)
        (algebraMap B (Spec (.of B)).functionField b)) = ψ b := by
  letI : IsDominant (rationalGraphProjectionCurve σX σB φ) :=
    rationalGraphProjectionCurve_isDominant σX σB φ
  have hSpecψ : IsDominant (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [← hφ]
    infer_instance
  letI : IsDominant (Spec.map (CommRingCat.ofHom ψ)) := hSpecψ
  have hg := rationalGraphImageFunctionFieldEquiv_comp_curve σX σB φ
  have hmap := @coordinateFieldMap_congr
    (Spec X.functionField) (Spec (.of B)) inferInstance inferInstance
    (rationalGraphGenericArrow σX σB φ) (Spec.map (CommRingCat.ofHom ψ))
    inferInstance hSpecψ hφ
  have hc := congrArg
    (fun f : (Spec (.of B)).functionField ⟶ (Spec X.functionField).functionField ↦
      (affineCoordinateFunctionFieldEquiv X.functionField X.functionField).toRingHom.comp
        f.hom)
    hmap
  have hh := hg.trans hc
  have hb := congrArg
    (fun f : (Spec (.of B)).functionField →+* X.functionField ↦
      f (algebraMap B (Spec (.of B)).functionField b)) hh
  change rationalGraphImageFunctionFieldEquiv σX σB φ
      (dominantFunctionFieldMap (rationalGraphProjectionCurve σX σB φ)
        (algebraMap B (Spec (.of B)).functionField b)) =
    affineGenericFieldMap B X.functionField ψ hψ
      (algebraMap B (Spec (.of B)).functionField b) at hb
  exact hb.trans (affineGenericFieldMap_algebraMap B X.functionField ψ hψ b)

end GraphCoordinates

section ActualScalars

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual structural square proves scalar compatibility after
composing the native field map with an actual base-field equivalence. -/
theorem actualFieldEquiv_comp_dominantFunctionFieldMap_scalar
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsDominant f] (hstructure : f ≫ σY = σX) :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    ∀ (e : X.functionField ≃ₐ[k] F) (c : k),
      e (dominantFunctionFieldMap f (algebraMap k Y.functionField c)) =
        algebraMap k F c := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  intro e c
  have hc := congrArg (fun g : (.of k) ⟶ X.functionField ↦ g c)
    (structureFunctionFieldScalarHom_comp_dominantFunctionFieldMap σX σY f hstructure)
  change dominantFunctionFieldMap f (algebraMap k Y.functionField c) =
    algebraMap k X.functionField c at hc
  rw [hc]
  exact e.commutes c

end ActualScalars

end

end ChenRanks
