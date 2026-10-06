import ChenRanks.StructureFunctionFieldTower
import ChenRanks.VerticalProperFunctions

/-!
# Absolute differentials from the actual proper-fibre mechanism

The original base-field scalar actions and their actual scalar tower are
derived from the actual structure square. The actual Kähler transitivity
sequence then turns the proved proper generic-fibre algebraicity into
membership in the actual base-change differential range.

The retained affine-order hypothesis is still the one on all actual
height-one primes of the actual normal charts. Its derivation from the
paper's horizontal divisor list, together with construction of the
paper's smooth/projective model, is not asserted here.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- An actual regular germ over a nonempty base open has its actual
absolute differential in the base function field's actual differential
range. No scalar compatibility, function-field comparison, or relative
differential vanishing is supplied as a premise. -/
theorem regular_absolute_differential_mem_baseChange_range
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    [IsProper σX] [IsSeparated σY] (f : X ⟶ Y) [IsDominant f]
    (hstructure : f ≫ σY = σX)
    (W : Y.Opens) [Nonempty W] (s : X.presheaf.obj (op (f ⁻¹ᵁ W))) :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    KaehlerDifferential.D k X.functionField (X.germToFunctionField (f ⁻¹ᵁ W) s) ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange k Y.functionField X.functionField) := by
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  letI : IsProper f := proper_of_structure_comp f σX σY hstructure
  letI : CharZero Y.functionField := functionField_charZero_from_structure σY
  exact algebraic_differential_mem_baseChange_range k _
    (regular_germ_isAlgebraic_over_baseFunctionField f W s)

variable [IsLocallyNoetherian X]

/-- The actual integer combination of logarithmic differentials lies
in the actual base differential range. The actual affine-order kernel
first constructs a regular unit and the proper generic-fibre mechanism
proves algebraicity of its actual integer product. -/
theorem integer_logarithmic_combination_mem_baseChange_range_of_affine_order_kernel
    (σX : X ⟶ Spec (.of k)) (σY : Y ⟶ Spec (.of k))
    [IsProper σX] [IsSeparated σY] (f : X ⟶ Y) [IsDominant f]
    (hstructure : f ≫ σY = σX)
    (W : Y.Opens) [Nonempty W] {ι : Type u} (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
    (hUV : ∀ i, U i ≤ f ⁻¹ᵁ W) (hcover : f ⁻¹ᵁ W ≤ iSup U)
    (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    {j : Type*} (s : Finset j) (F : j → X.functionFieldˣ) (n : j → ℤ)
    (hkernel : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      (∑ a ∈ s, n a * affineHeightOnePrimeOrder X (U i) (hAffine i)
        (hNormal i) p hp hh (F a : X.functionField)) = 0) :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    (∑ a ∈ s, n a • logarithmicDifferential k X.functionField (F a)) ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange k Y.functionField X.functionField) := by
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  letI : IsProper f := proper_of_structure_comp f σX σY hstructure
  letI : CharZero Y.functionField := functionField_charZero_from_structure σY
  rw [← logarithmicDifferential_prod_zpow]
  exact algebraic_logarithmic_differential_mem_baseChange_range k _
    (integer_product_isAlgebraic_of_affine_order_kernel
      f W U hAffine hUV hcover hNormal s F n hkernel)

end

end ChenRanks
