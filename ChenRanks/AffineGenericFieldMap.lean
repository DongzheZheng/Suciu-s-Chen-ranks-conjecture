import ChenRanks.CurveAffineRationalMap
import ChenRanks.DominantFunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual induced field maps of affine generic arrows

An actual injective coordinate-ring map B → K gives its actual dominant
Spec morphism.  The function-field map is the native generic-stalk map;
the field-spectrum comparison is constructed from the actual fraction
rings.  Its restriction to the actual coordinates is proved equal to the
original coordinate map.  This is the interface needed to identify the
curve projection with the original coefficient-field inclusion.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

section Composition

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- Actual dominant generic-stalk maps compose contravariantly. -/
theorem dominantFunctionFieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [IsDominant g] :
    dominantFunctionFieldMap g ≫ dominantFunctionFieldMap f =
      dominantFunctionFieldMap (f ≫ g) := by
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  rw [Spec.map_comp, Category.assoc, dominantFunctionFieldMap_spec_comp,
    ← Category.assoc, dominantFunctionFieldMap_spec_comp,
    Category.assoc, dominantFunctionFieldMap_spec_comp]

end Composition

section AffineGeneric

variable (B K : Type u) [CommRing B] [IsDomain B] [Field K]

omit [IsDomain B] in
/-- Actual coordinate injectivity gives actual dominance of its Spec
map.  Dominance is a conclusion, not a desired field-map premise. -/
theorem injectiveAffineGenericMorphism_isDominant (ψ : B →+* K)
    (hψ : Function.Injective ψ) : IsDominant (Spec.map (CommRingCat.ofHom ψ)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap ψ)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot ψ).mp hψ]
  exact bot_le

/-- The actual induced field map, followed by the actual field-spectrum
fraction comparison. -/
def affineGenericFieldMap (ψ : B →+* K) (hψ : Function.Injective ψ) :
    (Spec (.of B)).functionField →+* K := by
  letI : IsDominant (Spec.map (CommRingCat.ofHom ψ)) :=
    injectiveAffineGenericMorphism_isDominant B K ψ hψ
  exact (affineCoordinateFunctionFieldEquiv K K).toRingHom.comp
    (dominantFunctionFieldMap (Spec.map (CommRingCat.ofHom ψ))).hom

/-- The actual generic-stalk map restricts to the original coordinate
map, by the actual Spec/fromSpecStalk triangles. -/
theorem affineGenericFieldMap_algebraMap (ψ : B →+* K)
    (hψ : Function.Injective ψ) (b : B) :
    affineGenericFieldMap B K ψ hψ
      (algebraMap B (Spec (.of B)).functionField b) = ψ b := by
  letI : IsDominant (Spec.map (CommRingCat.ofHom ψ)) :=
    injectiveAffineGenericMorphism_isDominant B K ψ hψ
  have hs : CommRingCat.ofHom (algebraMap B (Spec (.of B)).functionField) ≫
      dominantFunctionFieldMap (Spec.map (CommRingCat.ofHom ψ)) =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K (Spec (.of K)).functionField) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    have hB : Spec.map (CommRingCat.ofHom (algebraMap B (Spec (.of B)).functionField)) =
        (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))) := by
      rw [Spec.fromSpecStalk_eq']
      rfl
    have hK : Spec.map (CommRingCat.ofHom (algebraMap K (Spec (.of K)).functionField)) =
        (Spec (.of K)).fromSpecStalk (genericPoint (Spec (.of K))) := by
      rw [Spec.fromSpecStalk_eq']
      rfl
    rw [hB, hK]
    exact dominantFunctionFieldMap_spec_comp (Spec.map (CommRingCat.ofHom ψ))
  have hb := congrArg (fun f : (.of B) ⟶ (Spec (.of K)).functionField => f b) hs
  change dominantFunctionFieldMap (Spec.map (CommRingCat.ofHom ψ))
      (algebraMap B (Spec (.of B)).functionField b) =
    algebraMap K (Spec (.of K)).functionField (ψ b) at hb
  change (affineCoordinateFunctionFieldEquiv K K)
    (dominantFunctionFieldMap (Spec.map (CommRingCat.ofHom ψ))
      (algebraMap B (Spec (.of B)).functionField b)) = ψ b
  rw [hb]
  exact (affineCoordinateFunctionFieldEquiv K K).commutes (ψ b)

end AffineGeneric

end

end ChenRanks
