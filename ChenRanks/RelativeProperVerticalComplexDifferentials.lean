import ChenRanks.VerticalComplexDifferentials

/-!
# The paper's vertical-kernel mechanism for an actual relatively proper model

The actual proper generic-fibre proof requires properness of the actual
map to the coefficient curve. It does not require properness of its
source over the original scalar field. This version uses that precise
hypothesis, allowing the actual normal graph over the actual affine
coefficient curve, while retaining the paper's integer-product and
absolute-differential argument.

The actual all-chart order-kernel condition still has to be proved from
horizontal residues after deleting the actual vertical support images.
No such condition is silently supplied by this theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

namespace ChenRanks

variable (X : Scheme) {ι : Type} (U : ι → X.Opens)

variable [IsIntegral X] [IsLocallyNoetherian X]
  [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
  (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
  {j : Type*} [Fintype j] (F : j → X.functionFieldˣ)

variable {Y : Scheme} [IsIntegral Y]

/-- The actual complex kernel has its actual absolute logarithmic
combination in the actual curve-field differential image. The integer
product algebraicity and finite detecting rows are both derived here. -/
theorem complex_logarithmic_combination_mem_baseChange_range_of_relative_proper_affine_order_kernel
    (σX : X ⟶ Spec (.of ℂ)) (σY : Y ⟶ Spec (.of ℂ))
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (hstructure : f ≫ σY = σX)
    (W : Y.Opens) [Nonempty W]
    (hUV : ∀ i, U i ≤ f ⁻¹ᵁ W) (hcover : f ⁻¹ᵁ W ≤ iSup U)
    (β : j → ℂ)
    (hβ : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, ∀ hh : p.height = 1,
      (∑ a, (affineHeightOnePrimeOrder X (U i) (hAffine i)
        (hNormal i) p hp hh (F a : X.functionField) : ℂ) * β a) = 0) :
    letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower ℂ Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    relativeLogCombination (L := ℂ) F β ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange ℂ Y.functionField X.functionField) := by
  classical
  letI : Algebra ℂ Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra ℂ X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower ℂ Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  letI : CharZero Y.functionField := functionField_charZero_from_structure σY
  let rows := affineOrderRows X U hAffine hNormal F
  obtain ⟨T, hspan⟩ := exists_finset_rational_rows_span rows
  let B : Matrix ↥T j ℤ := fun d a ↦ rows d.val a
  have hProducts : ∀ n : j → ℤ, B.mulVec n = 0 →
      IsAlgebraic Y.functionField ((∏ a, F a ^ n a : X.functionFieldˣ) : X.functionField) := by
    intro n hn
    have hselected : ∀ d ∈ T, integerRowDot rows n d = 0 := by
      intro d hd
      exact congrFun hn ⟨d, hd⟩
    have hall := (integer_kernel_iff_of_span_eq rows T hspan n).mp hselected
    apply integer_product_isAlgebraic_of_affine_order_kernel
      f W U hAffine hUV hcover hNormal Finset.univ F n
    intro i p hp hh
    simpa only [integerRowDot, rows, affineOrderRows, mul_comm] using
      hall ⟨i, ⟨p, hp, hh⟩⟩
  have hmatrix : (B.map (algebraMap ℤ ℂ)).mulVec β = 0 := by
    funext d
    exact hβ d.val.1 d.val.2.val d.val.2.property.1 d.val.2.property.2
  exact absoluteLogCombination_mem_baseChange_range_of_kernel_products_algebraic
    B F hProducts β hmatrix

end ChenRanks
