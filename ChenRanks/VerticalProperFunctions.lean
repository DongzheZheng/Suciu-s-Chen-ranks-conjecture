import ChenRanks.GenericFibreRegularFunctions
import ChenRanks.VerticalRegularSections
import ChenRanks.LogarithmicDifferentials

/-!
# Actual affine order kernels and the proper-fibre conclusion

This file composes the proved actual height-one order-to-section theorem
with the actual proper generic-fibre theorem. The actual integer product
is algebraic over the actual base function field, and hence its actual
relative logarithmic differential vanishes in characteristic zero.

The geometric inputs retained here are actual normal affine charts over
the inverse image of an actual nonempty base open, and vanishing of all
their actual height-one order rows. This does not assert that the paper's
horizontal-divisor kernel has already supplied those rows after deletion
of finitely many vertical images. No such geometric implication is used
as an unproved definition or as the conclusion of this file.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]

/-- The actual order kernel constructs a regular section, and the
actual proper generic fibre then proves algebraicity of its actual
integer-product germ over the actual base function field. -/
theorem integer_product_isAlgebraic_of_affine_order_kernel
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (W : Y.Opens) [Nonempty W] {ι : Type u} (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
    (hUV : ∀ i, U i ≤ f ⁻¹ᵁ W) (hcover : f ⁻¹ᵁ W ≤ iSup U)
    (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    {j : Type*} (s : Finset j) (F : j → X.functionFieldˣ) (n : j → ℤ)
    (hkernel : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      (∑ a ∈ s, n a * affineHeightOnePrimeOrder X (U i) (hAffine i)
        (hNormal i) p hp hh (F a : X.functionField)) = 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    IsAlgebraic Y.functionField
      ((∏ a ∈ s, F a ^ n a : X.functionFieldˣ) : X.functionField) := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  obtain ⟨t, ht, _⟩ := exists_regular_unit_section_of_affine_order_integer_kernel
    X (f ⁻¹ᵁ W) U hAffine hUV hcover hNormal s F n hkernel
  have h := regular_germ_isAlgebraic_over_baseFunctionField f W t
  rwa [ht] at h

/-- The relative differential of the actual integer product vanishes
by the preceding actual algebraicity theorem, not by a verticality premise. -/
theorem integer_product_relative_differential_eq_zero_of_affine_order_kernel
    [CharZero Y.functionField]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (W : Y.Opens) [Nonempty W] {ι : Type u} (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
    (hUV : ∀ i, U i ≤ f ⁻¹ᵁ W) (hcover : f ⁻¹ᵁ W ≤ iSup U)
    (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    {j : Type*} (s : Finset j) (F : j → X.functionFieldˣ) (n : j → ℤ)
    (hkernel : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      (∑ a ∈ s, n a * affineHeightOnePrimeOrder X (U i) (hAffine i)
        (hNormal i) p hp hh (F a : X.functionField)) = 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    KaehlerDifferential.D Y.functionField X.functionField
      ((∏ a ∈ s, F a ^ n a : X.functionFieldˣ) : X.functionField) = 0 := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  exact relative_differential_eq_zero_of_isAlgebraic _
    (integer_product_isAlgebraic_of_affine_order_kernel
      f W U hAffine hUV hcover hNormal s F n hkernel)

/-- The actual integral combination of actual logarithmic
differentials has zero relative image, using the actual product identity. -/
theorem integer_logarithmic_combination_eq_zero_of_affine_order_kernel
    [CharZero Y.functionField]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (W : Y.Opens) [Nonempty W] {ι : Type u} (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
    (hUV : ∀ i, U i ≤ f ⁻¹ᵁ W) (hcover : f ⁻¹ᵁ W ≤ iSup U)
    (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    {j : Type*} (s : Finset j) (F : j → X.functionFieldˣ) (n : j → ℤ)
    (hkernel : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      (∑ a ∈ s, n a * affineHeightOnePrimeOrder X (U i) (hAffine i)
        (hNormal i) p hp hh (F a : X.functionField)) = 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    (∑ a ∈ s, n a • logarithmicDifferential Y.functionField X.functionField (F a)) = 0 := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  rw [← logarithmicDifferential_prod_zpow]
  change (((∏ a ∈ s, F a ^ n a : X.functionFieldˣ) : X.functionField))⁻¹ •
    KaehlerDifferential.D Y.functionField X.functionField
      ((∏ a ∈ s, F a ^ n a : X.functionFieldˣ) : X.functionField) = 0
  rw [integer_product_relative_differential_eq_zero_of_affine_order_kernel
    f W U hAffine hUV hcover hNormal s F n hkernel, smul_zero]

variable {k : Type u} [Field k] [CharZero k]

/-- The actual original structure morphisms supply properness and
characteristic zero for this same affine-order conclusion. -/
theorem integer_product_relative_differential_eq_zero_of_proper_source_order_kernel
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
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    KaehlerDifferential.D Y.functionField X.functionField
      ((∏ a ∈ s, F a ^ n a : X.functionFieldˣ) : X.functionField) = 0 := by
  letI : IsProper f := proper_of_structure_comp f σX σY hstructure
  letI : CharZero Y.functionField := functionField_charZero_from_structure σY
  exact integer_product_relative_differential_eq_zero_of_affine_order_kernel
    f W U hAffine hUV hcover hNormal s F n hkernel

end

end ChenRanks
