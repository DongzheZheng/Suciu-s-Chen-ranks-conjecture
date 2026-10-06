import ChenRanks.RationalGraphImage
import ChenRanks.StructureFunctionFieldTower

/-!
# The actual graph function field and its original scalar action

The field comparison is constructed from the actual dominant
preimmersion from the native field spectrum into the native graph image,
followed by the actual affine fraction-ring comparison.  Its inverse is
proved to be the actual graph projection's generic-stalk map.  Original
scalar compatibility is then derived from the actual structure square.
Neither a field equivalence nor its scalar compatibility is an input.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X C S : Scheme.{u}} [IsIntegral X]
  (σX : X ⟶ S) (σC : C ⟶ S) [LocallyOfFiniteType σC]
  (φ : {r : X.RationalMap C // r.compHom σC = σX.toRationalMap})

/-- The actual graph function field is the original actual source
function field, by two constructed native comparisons. -/
def rationalGraphImageFunctionFieldEquiv :
    (rationalGraphImage σX σC φ).functionField ≃+* X.functionField :=
  (dominantPreimmersionFunctionFieldEquiv (rationalGraphToImage σX σC φ)).trans
    (affineCoordinateFunctionFieldEquiv (X.functionField : Type u)
      (X.functionField : Type u)).toRingEquiv

/-- The actual projection and actual image-factor generic-stalk maps
compose to the native scalar map into the actual field spectrum's
function field.  The proof uses actual Spec/generic-stalk triangles. -/
theorem rationalGraphFunctionFieldMap_comp :
    dominantFunctionFieldMap (rationalGraphProjectionSource σX σC φ) ≫
        dominantFunctionFieldMap (rationalGraphToImage σX σC φ) =
      CommRingCat.ofHom (algebraMap (X.functionField : Type u)
        (Spec X.functionField).functionField) := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  rw [Spec.map_comp, Category.assoc, dominantFunctionFieldMap_spec_comp,
    ← Category.assoc, dominantFunctionFieldMap_spec_comp,
    Category.assoc, rationalGraphToImage_projectionSource]
  rw [Spec.fromSpecStalk_eq']
  rfl

/-- The inverse of the constructed equivalence is precisely the actual
source projection map, not an unrelated isomorphism of abstract fields. -/
theorem rationalGraphImageFunctionFieldEquiv_symm_eq_projection :
    (rationalGraphImageFunctionFieldEquiv σX σC φ).symm.toRingHom =
      (dominantFunctionFieldMap (rationalGraphProjectionSource σX σC φ)).hom := by
  ext x
  apply (rationalGraphImageFunctionFieldEquiv σX σC φ).injective
  change (rationalGraphImageFunctionFieldEquiv σX σC φ)
      ((rationalGraphImageFunctionFieldEquiv σX σC φ).symm x) =
    (rationalGraphImageFunctionFieldEquiv σX σC φ)
      (dominantFunctionFieldMap (rationalGraphProjectionSource σX σC φ) x)
  rw [RingEquiv.apply_symm_apply]
  change x = (affineCoordinateFunctionFieldEquiv (X.functionField : Type u)
    (X.functionField : Type u))
      (dominantFunctionFieldMap (rationalGraphToImage σX σC φ)
        (dominantFunctionFieldMap (rationalGraphProjectionSource σX σC φ) x))
  have hx := congrArg (fun h : X.functionField ⟶ (Spec X.functionField).functionField => h x)
    (rationalGraphFunctionFieldMap_comp σX σC φ)
  change dominantFunctionFieldMap (rationalGraphToImage σX σC φ)
      (dominantFunctionFieldMap (rationalGraphProjectionSource σX σC φ) x) =
    algebraMap (X.functionField : Type u) (Spec X.functionField).functionField x at hx
  rw [hx]
  exact ((affineCoordinateFunctionFieldEquiv (X.functionField : Type u)
    (X.functionField : Type u)).commutes x).symm

/-- The actual graph structure morphism uses the actual source
projection. -/
def rationalGraphScalarMorphism : rationalGraphImage σX σC φ ⟶ S :=
  rationalGraphProjectionSource σX σC φ ≫ σX

@[reassoc]
theorem rationalGraphProjectionCurve_structure :
    rationalGraphProjectionCurve σX σC φ ≫ σC = rationalGraphScalarMorphism σX σC φ := by
  simp only [rationalGraphProjectionCurve, rationalGraphProjectionSource,
    rationalGraphScalarMorphism, Category.assoc]
  rw [← Limits.pullback.condition]

end

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {X C : Scheme.{u}} [IsIntegral X]
  (σX : X ⟶ Spec (.of k)) (σC : C ⟶ Spec (.of k)) [LocallyOfFiniteType σC]
  (φ : {r : X.RationalMap C // r.compHom σC = σX.toRationalMap})

/-- The actual inverse graph comparison preserves the actual original
base-field scalar structures, because its ring map is the actual
projection map and the actual structure square commutes. -/
def rationalGraphSourceFunctionFieldAlgEquiv :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
      structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
    X.functionField ≃ₐ[k] (rationalGraphImage σX σC φ).functionField := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
    structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
  refine { (rationalGraphImageFunctionFieldEquiv σX σC φ).symm with commutes' := ?_ }
  intro c
  change (rationalGraphImageFunctionFieldEquiv σX σC φ).symm.toRingHom
      (structureFunctionFieldScalarHom σX c) =
    structureFunctionFieldScalarHom (rationalGraphScalarMorphism σX σC φ) c
  rw [rationalGraphImageFunctionFieldEquiv_symm_eq_projection]
  exact congrArg (fun h : (.of k) ⟶ (rationalGraphImage σX σC φ).functionField => h c)
    (structureFunctionFieldScalarHom_comp_dominantFunctionFieldMap
      (rationalGraphScalarMorphism σX σC φ) σX (rationalGraphProjectionSource σX σC φ) rfl)

/-- The constructed graph-to-original field comparison with the actual
original scalar action. -/
def rationalGraphImageFunctionFieldAlgEquiv :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
      structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
    (rationalGraphImage σX σC φ).functionField ≃ₐ[k] X.functionField := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra k (rationalGraphImage σX σC φ).functionField :=
    structureFunctionFieldAlgebra (rationalGraphScalarMorphism σX σC φ)
  exact (rationalGraphSourceFunctionFieldAlgEquiv σX σC φ).symm

end

end ChenRanks
