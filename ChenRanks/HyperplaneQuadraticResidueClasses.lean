import ChenRanks.HyperplaneQuadraticKernelRows
import ChenRanks.HyperplaneRestrictedDegrees
import ChenRanks.AffinePolynomialLogarithmicClasses

/-!
# Actual restricted-divisor classes detected in the original quadratic kernel

Every original quadratic-kernel element has the actual restricted dlog
row, proved by actual two-form residues with the constructed regular
remainder. All other equations restrict to actual nonzero affine
polynomials. A genuinely nonparallel selected pair gives an actual
degree-one restricted equation. Applying the independently constructed
one-form class residue forces coefficient sum zero on its actual
restricted-divisor class.

The class is literal polynomial divisibility in the original pivot ring.
The proved proportional-restriction criterion relates it to actual affine
three-equation relations, retaining offsets. A later exterior-block
argument is still needed for the complete quadratic-kernel identification.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance hyperplaneQuadraticClasses_propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance hyperplaneQuadraticClasses_pivotAlgebra (j : Fin d) :
    Algebra ℂ (HyperplanePivotField j) := hyperplanePivotField_complexAlgebra j

local instance hyperplaneQuadraticClasses_pivotSMul (j : Fin d) :
    SMul ℂ (HyperplanePivotField j) :=
  (hyperplaneQuadraticClasses_pivotAlgebra j).toSMul

local instance hyperplaneQuadraticClasses_pivotConstantComm (j : Fin d) :
    SMulCommClass ℂ ℂ (HyperplanePivotField j) where
  smul_comm a b x := by
    change algebraMap ℂ (HyperplanePivotField j) a *
        (algebraMap ℂ (HyperplanePivotField j) b * x) =
      algebraMap ℂ (HyperplanePivotField j) b *
        (algebraMap ℂ (HyperplanePivotField j) a * x)
    exact mul_left_comm _ _ _

local instance hyperplaneQuadraticClasses_pivotDifferentialModule (j : Fin d) :
    Module ℂ Ω[HyperplanePivotField j⁄ℂ] :=
  KaehlerDifferential.module' ℂ (HyperplanePivotField j)

local instance hyperplaneQuadraticClasses_pivotDifferentialSMul (j : Fin d) :
    SMul ℂ Ω[HyperplanePivotField j⁄ℂ] :=
  (hyperplaneQuadraticClasses_pivotDifferentialModule j).toSMul

set_option maxHeartbeats 400000 in
/-- Genuine original quadratic-kernel elements have zero coordinate-row
sum on each actual nonconstant restricted divisor class. No logarithmic
independence or divisor-class partition is an input. -/
theorem rationalQuadraticKernel_restrictedDivisorClass_row_sum_zero
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hz : z ∈ A.rationalQuadraticKernel)
    (H K₀ : ι) (hHK : H ≠ K₀) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0)
    (hparallel : ¬∃ c : ℂ, A.normal K₀ = c • A.normal H) :
    (∑ K ∈ Finset.univ.filter (fun K : {K : ι // K ≠ H} ↦
      A.hyperplanePivotRestriction H j (A.equationPolynomial K₀) ∣
        A.hyperplanePivotRestriction H j (A.equationPolynomial K.val)),
      Koszul.coordinateExteriorRow ℂ ι H z K.val) = 0 := by
  classical
  let q : {K : ι // K ≠ H} → HyperplanePivotRing j :=
    fun K ↦ A.hyperplanePivotRestriction H j (A.equationPolynomial K.val)
  have hq : ∀ K, q K ≠ 0 := fun K ↦
    A.hyperplanePivotRestriction_other_ne_zero H K.val K.property.symm j hj
  have hdegree : ∀ K, (q K).totalDegree ≤ 1 := fun K ↦
    A.hyperplanePivotRestriction_equation_totalDegree_le_one H K.val j
  have hrow := A.rationalQuadraticKernel_pivot_logarithmic_rows z hz H j hj
  have hunit (K : {K : ι // K ≠ H}) :
      A.hyperplaneRestrictedEquationUnit H K.val K.property.symm j hj =
        affinePolynomialFractionUnit ℂ {i : Fin d // i ≠ j} (q K) (hq K) := by
    apply Units.ext
    rfl
  have hrelation : (∑ K : {K : ι // K ≠ H},
      Koszul.coordinateExteriorRow ℂ ι H z K.val •
        logarithmicDifferential ℂ (FractionRing (HyperplanePivotRing j))
          (affinePolynomialFractionUnit ℂ {i : Fin d // i ≠ j} (q K) (hq K))) = 0 := by
    have hsum : (∑ K : {K : ι // K ≠ H},
        Koszul.coordinateExteriorRow ℂ ι H z K.val •
          logarithmicDifferential ℂ (FractionRing (HyperplanePivotRing j))
            (affinePolynomialFractionUnit ℂ {i : Fin d // i ≠ j} (q K) (hq K))) =
        ∑ K : {K : ι // K ≠ H},
          Koszul.coordinateExteriorRow ℂ ι H z K.val •
            logarithmicDifferential ℂ (HyperplanePivotField j)
              (A.hyperplaneRestrictedEquationUnit H K.val K.property.symm j hj) := by
      apply Finset.sum_congr rfl
      intro K _
      rw [← hunit K]
    exact hsum.trans hrow
  have hselected : (q ⟨K₀, hHK.symm⟩).totalDegree = 1 :=
    A.hyperplanePivotRestriction_totalDegree_eq_one_of_not_parallel H K₀ j hj hparallel
  exact affinePolynomialLogarithmicRelation_divisorClass_sum_zero
    ℂ {i : Fin d // i ≠ j} q hq hdegree
      (fun K ↦ Koszul.coordinateExteriorRow ℂ ι H z K.val) hrelation
        ⟨K₀, hHK.symm⟩ hselected

end ChenRanks.AffineArrangement
