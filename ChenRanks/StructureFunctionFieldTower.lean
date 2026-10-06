import ChenRanks.GenericFibreAlgebraicity

/-!
# The actual scalar tower of a morphism over the original base field

The two scalar actions come from the two actual structure morphisms,
and the function-field map comes from the actual dominant morphism.
Their compatibility is proved from the actual commutative structure
square, using the actual generic-stalk maps and Spec faithfulness.
It is not an additional compatibility premise.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual map of function fields respects the actual original
base-field scalar maps because the original structure square commutes. -/
theorem structureFunctionFieldScalarHom_comp_dominantFunctionFieldMap
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsDominant f] (hstructure : f ≫ σY = σX) :
    structureFunctionFieldScalarHom σY ≫ dominantFunctionFieldMap f =
      structureFunctionFieldScalarHom σX := by
  apply Spec.map_injective
  calc
    Spec.map (structureFunctionFieldScalarHom σY ≫ dominantFunctionFieldMap f) =
        Spec.map (dominantFunctionFieldMap f) ≫
          (Y.fromSpecStalk (genericPoint Y) ≫ σY) := by
      rw [Spec.map_comp, structureFunctionFieldScalarHom_spec]
    _ = (X.fromSpecStalk (genericPoint X) ≫ f) ≫ σY := by
      rw [← Category.assoc, dominantFunctionFieldMap_spec_comp]
    _ = X.fromSpecStalk (genericPoint X) ≫ σX := by
      rw [Category.assoc, hstructure]
    _ = Spec.map (structureFunctionFieldScalarHom σX) := by
      rw [structureFunctionFieldScalarHom_spec]

/-- The same actual three algebra structures form an actual scalar
tower. The tower property is a conclusion of the proved scalar-map
identity, not an assumption about an unidentified field comparison. -/
theorem functionFieldScalarTower_of_structure_square
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsDominant f] (hstructure : f ≫ σY = σX) :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    IsScalarTower k Y.functionField X.functionField := by
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change structureFunctionFieldScalarHom σX a =
    dominantFunctionFieldMap f (structureFunctionFieldScalarHom σY a)
  exact (congrArg (fun h : (.of k) ⟶ X.functionField => h a)
    (structureFunctionFieldScalarHom_comp_dominantFunctionFieldMap σX σY f hstructure)).symm

end

end ChenRanks
