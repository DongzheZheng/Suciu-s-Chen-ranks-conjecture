import ChenRanks.VerticalAbsoluteDifferentials
import ChenRanks.ValuationKernelDifferentials
import ChenRanks.FiniteValuationRows

/-!
# Actual complex order kernels and actual vertical logarithmic forms

The actual row family contains every actual height-one prime of every
actual normal affine chart of the actual inverse-image open. Its index
set need not be finite. The proved rational row-span theorem chooses a
finite subset of those same indices and detects all integral vectors.

The actual proper-fibre theorem supplies algebraicity for the genuine
integral products. The proved integer-kernel scalar-extension theorem
then proves the complex logarithmic combination lies in the actual
base-change differential image. Product algebraicity is a conclusion.

The passage from the paper's horizontal divisor rows to these chart
rows, and construction of the model, remain explicit geometric work.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

namespace ChenRanks

variable (X : Scheme) {ι : Type} (U : ι → X.Opens)

/-- All actual chart height-one primes, rather than a supplied sample. -/
abbrev affineOrderRowIndex (X : Scheme) {ι : Type} (U : ι → X.Opens) : Type :=
  Σ i : ι, {p : Ideal (X.presheaf.obj (Opposite.op (U i))) // p.IsPrime ∧ p.height = 1}

variable [IsIntegral X] [IsLocallyNoetherian X]
  [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
  (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
  {j : Type*} [Fintype j] (F : j → X.functionFieldˣ)

/-- The entries are the already constructed actual normalized chart orders. -/
def affineOrderRows : affineOrderRowIndex X U → j → ℤ := fun d a ↦
  affineHeightOnePrimeOrder X (U d.1) (hAffine d.1) (hNormal d.1)
    d.2.val d.2.property.1 d.2.property.2 (F a : X.functionField)

variable {Y : Scheme} [IsIntegral Y]

/-- The actual complex kernel has its actual absolute logarithmic
combination in the actual curve-field differential image. The integer
product algebraicity and finite detecting rows are both derived here. -/
theorem complex_logarithmic_combination_mem_baseChange_range_of_affine_order_kernel
    (σX : X ⟶ Spec (.of ℂ)) (σY : Y ⟶ Spec (.of ℂ))
    [IsProper σX] [IsSeparated σY] (f : X ⟶ Y) [IsDominant f]
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
  letI : IsProper f := proper_of_structure_comp f σX σY hstructure
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
