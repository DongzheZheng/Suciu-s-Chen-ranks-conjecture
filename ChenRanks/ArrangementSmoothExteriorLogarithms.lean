import ChenRanks.ArrangementSmoothEquationUnits
import ChenRanks.ArrangementSmoothExteriorComplex
import ChenRanks.OpenSmoothExteriorLeibniz
import ChenRanks.ArrangementLogarithmicMeridianPeriods

/-!
# Genuine normalized logarithms in the actual coefficient exterior ring

Each coefficient is the proved smooth reciprocal of its original affine
equation.  Its constant covector consists of the original normal evaluated
on the constructed real basis.  Native coefficient differentiation and
native exterior anti-commutation prove closedness and the square-zero
condition for the true universal exterior-algebra map.  The normalization
is the genuine inverse of `2πi`, matching the actual meridian integral.
No relation-killing, de Rham comparison, or formality conclusion is assumed
or asserted here.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.AffineArrangement

open OpenSmoothFunctions OpenSmoothExterior

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance smoothExteriorLogLabelDecidableEq : DecidableEq ι := Classical.decEq ι

local instance smoothExteriorLogCoefficientCommRing :
    CommRing (SmoothFunction A.actualSmoothComplementOpen) :=
  inferInstanceAs (CommRing ↥(algebra A.actualSmoothComplementOpen))

local instance smoothExteriorLogConstantRing : Ring (ConstantExterior (Fin d × Fin 2)) :=
  inferInstanceAs (Ring (ExteriorAlgebra ℂ ((Fin d × Fin 2) → ℂ)))

local instance smoothExteriorLogActualTensorRing : Ring A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.instRing (R := ℂ)
    (A := SmoothFunction A.actualSmoothComplementOpen) (B := ConstantExterior (Fin d × Fin 2))

local instance smoothExteriorLogActualTensorNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring A.ActualSmoothCoefficientExterior :=
  (smoothExteriorLogActualTensorRing A).toSemiring.toNonAssocSemiring.toNonUnitalNonAssocSemiring

local instance smoothExteriorLogActualTensorModule : Module ℂ A.ActualSmoothCoefficientExterior :=
  inferInstanceAs (Module ℂ
    (SmoothFunction A.actualSmoothComplementOpen ⊗[ℂ] ConstantExterior (Fin d × Fin 2)))

local instance smoothExteriorLogActualTensorSMul : SMul ℂ A.ActualSmoothCoefficientExterior :=
  (smoothExteriorLogActualTensorModule A).toSMul

/-- The true constant covector of an original hyperplane in the actual
constructed real-coordinate basis. -/
def actualSmoothExteriorNormal (H : ι) : (Fin d × Fin 2) → ℂ :=
  fun i => A.normal H (complexAffineRealBasis d i)

/-- The genuine unnormalized logarithm in the literal coefficient ring. -/
def actualSmoothExteriorLogarithm (H : ι) : A.ActualSmoothCoefficientExterior :=
  A.actualSmoothEquationInverse H ⊗ₜ[ℂ]
    ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H)

/-- The genuine period-one normalization, with the proved actual period
constant rather than a formal identification with integer winding. -/
def actualNormalizedSmoothExteriorLogarithm (H : ι) :
    A.ActualSmoothCoefficientExterior :=
  logarithmicPeriodConstant⁻¹ • A.actualSmoothExteriorLogarithm H

/-- Constant coordinate covectors recombine to the actual original normal. -/
theorem actualSmoothExteriorNormal_generators (H : ι) :
    (∑ i : Fin d × Fin 2,
      A.actualSmoothExteriorNormal H i • generator i) =
        ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H) := by
  classical
  simp only [generator, ← map_smul, ← map_sum]
  congr 1
  funext j
  simp [Pi.single_apply]

/-- The logarithm is an actual degree-one element of the actual tensor
image grading. -/
theorem actualSmoothExteriorLogarithm_mem_degree_one (H : ι) :
    A.actualSmoothExteriorLogarithm H ∈
      homogeneousSubmodule A.actualSmoothComplementOpen (Fin d × Fin 2) 1 := by
  have hι : ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H) ∈
      ⋀[ℂ]^1 ((Fin d × Fin 2) → ℂ) := by
    simpa only [pow_one] using
      LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) (A.actualSmoothExteriorNormal H)
  refine ⟨A.actualSmoothEquationInverse H ⊗ₜ[ℂ]
    ⟨ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H), hι⟩, ?_⟩
  exact homogeneousInclusion_tmul A.actualSmoothComplementOpen 1 _ _

/-- Actual inverse calculus makes its derivative a multiple of the
square of its original normal, which vanishes in the native exterior ring. -/
theorem actualSmoothExteriorLogarithm_differential_eq_zero (H : ι) :
    A.actualSmoothCoefficientExteriorDifferential
      (A.actualSmoothExteriorLogarithm H) = 0 := by
  unfold actualSmoothCoefficientExteriorDifferential actualSmoothExteriorLogarithm
  rw [differential_tmul]
  have hc (i : Fin d × Fin 2) :
      directional A.actualSmoothComplementOpen (complexAffineRealBasis d i)
        (A.actualSmoothEquationInverse H) =
      A.actualSmoothExteriorNormal H i •
        (-(A.actualSmoothEquationInverse H * A.actualSmoothEquationInverse H)) := by
    change directionalLinearMap A.actualSmoothComplementOpen (complexAffineRealBasis d i)
      (A.actualSmoothEquationInverse H) = _
    rw [A.actualSmoothEquationInverse_directional]
    rw [Algebra.smul_def]
    exact mul_comm _ _
  simp only [hc, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum]
  have hsum : (∑ i : Fin d × Fin 2,
      A.actualSmoothExteriorNormal H i •
        (generator i * ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H))) = 0 := by
    simp only [← smul_mul_assoc]
    rw [← Finset.sum_mul, actualSmoothExteriorNormal_generators,
      ExteriorAlgebra.ι_sq_zero]
  rw [hsum, TensorProduct.tmul_zero]

/-- The normalized actual logarithm remains closed under the same actual
coefficient differential. -/
theorem actualNormalizedSmoothExteriorLogarithm_differential_eq_zero (H : ι) :
    A.actualSmoothCoefficientExteriorDifferential
      (A.actualNormalizedSmoothExteriorLogarithm H) = 0 := by
  rw [actualNormalizedSmoothExteriorLogarithm, map_smul,
    actualSmoothExteriorLogarithm_differential_eq_zero, smul_zero]

/-- True logarithm anti-commutation, including equal hyperplanes. -/
theorem actualSmoothExteriorLogarithms_anticommute (H K : ι) :
    A.actualSmoothExteriorLogarithm H * A.actualSmoothExteriorLogarithm K +
      A.actualSmoothExteriorLogarithm K * A.actualSmoothExteriorLogarithm H = 0 := by
  unfold actualSmoothExteriorLogarithm
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_comm (A.actualSmoothEquationInverse K) (A.actualSmoothEquationInverse H),
    ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap, TensorProduct.tmul_zero]

/-- The true linear map from the original hyperplane-label space. -/
def actualNormalizedSmoothExteriorGeneratorMap :
    (ι → ℂ) →ₗ[ℂ] A.ActualSmoothCoefficientExterior :=
  ∑ H : ι, (LinearMap.proj H).smulRight (A.actualNormalizedSmoothExteriorLogarithm H)

@[simp] theorem actualNormalizedSmoothExteriorGeneratorMap_apply (a : ι → ℂ) :
    A.actualNormalizedSmoothExteriorGeneratorMap a =
      ∑ H : ι, a H • A.actualNormalizedSmoothExteriorLogarithm H := by
  simp [actualNormalizedSmoothExteriorGeneratorMap]

theorem actualNormalizedSmoothExteriorGeneratorMap_closed (a : ι → ℂ) :
    A.actualSmoothCoefficientExteriorDifferential
      (A.actualNormalizedSmoothExteriorGeneratorMap a) = 0 := by
  rw [actualNormalizedSmoothExteriorGeneratorMap_apply, map_sum]
  simp only [map_smul, actualNormalizedSmoothExteriorLogarithm_differential_eq_zero,
    smul_zero, Finset.sum_const_zero]

/-- Native anti-commutation and characteristic zero prove the actual
square-zero hypothesis needed by the universal exterior constructor. -/
theorem actualNormalizedSmoothExteriorGeneratorMap_sq_zero (a : ι → ℂ) :
    A.actualNormalizedSmoothExteriorGeneratorMap a *
      A.actualNormalizedSmoothExteriorGeneratorMap a = 0 := by
  classical
  let x : ι → A.ActualSmoothCoefficientExterior := fun H =>
    a H • A.actualNormalizedSmoothExteriorLogarithm H
  have hp (H K : ι) : x H * x K + x K * x H = 0 := by
    dsimp only [x, actualNormalizedSmoothExteriorLogarithm]
    simp only [smul_smul, smul_mul_assoc, mul_smul_comm]
    rw [mul_comm (a K * logarithmicPeriodConstant⁻¹)
      (a H * logarithmicPeriodConstant⁻¹), ← smul_add,
      actualSmoothExteriorLogarithms_anticommute, smul_zero]
  have hs : (∑ H : ι, ∑ K : ι, (x H * x K + x K * x H)) = 0 := by
    simp only [hp, Finset.sum_const_zero]
  have hswap : (∑ H : ι, ∑ K : ι, x K * x H) =
      ∑ H : ι, ∑ K : ι, x H * x K := Finset.sum_comm
  simp only [Finset.sum_add_distrib] at hs
  rw [hswap] at hs
  have hz : (∑ H : ι, ∑ K : ι, x H * x K) = 0 :=
    (smul_eq_zero.mp (show (2 : ℂ) • (∑ H : ι, ∑ K : ι, x H * x K) = 0 by
      simpa only [two_smul] using hs)).resolve_left (by norm_num)
  rw [actualNormalizedSmoothExteriorGeneratorMap_apply, Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact hz

/-- The genuine native universal exterior-algebra map on the original
label space, constructed using the proved square-zero law above. -/
def actualNormalizedSmoothLogExteriorHom :
    ExteriorAlgebra ℂ (ι → ℂ) →ₐ[ℂ] A.ActualSmoothCoefficientExterior :=
  ExteriorAlgebra.lift ℂ ⟨A.actualNormalizedSmoothExteriorGeneratorMap,
    A.actualNormalizedSmoothExteriorGeneratorMap_sq_zero⟩

@[simp] theorem actualNormalizedSmoothLogExteriorHom_iota (a : ι → ℂ) :
    A.actualNormalizedSmoothLogExteriorHom (ExteriorAlgebra.ι ℂ a) =
      A.actualNormalizedSmoothExteriorGeneratorMap a := by
  exact ExteriorAlgebra.lift_ι_apply ℂ _ _ a

end ChenRanks.AffineArrangement
