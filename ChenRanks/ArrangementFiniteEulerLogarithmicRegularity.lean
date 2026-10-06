import ChenRanks.ArrangementFiniteEulerLogarithmicCoefficients
import ChenRanks.OpenSmoothSymmetricOneFormDerivative
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Actual infinite smoothness and closedness of the finite Euler coefficient form

All coefficients are the original normalized reciprocal affine equations.
Actual inverse differentiation gives their original real derivatives.
The finite sum of those derivatives is symmetric on its two original
tangent arguments. Native exterior differentiation therefore vanishes.
No smoothness, closedness or local flat-connection specification is selected
as an input; the assertion is made on the actual original open complement.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance finiteLogRegularityNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteLogRegularityNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteLogRegularityRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteLogRegularityScalarTower : IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a x := by
    change ((r : ℂ) * a) • x = (r : ℂ) • (a • x)
    exact mul_smul _ _ _
local instance finiteLogRegularitySMulCommClass : SMulCommClass ℂ ℝ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_comm a r x := by
    change a • ((r : ℂ) • x) = (r : ℂ) • (a • x)
    exact smul_comm _ _ _

local instance finiteLogRegularityCoefficientRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance finiteLogRegularityCoefficientComplexNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  inferInstanceAs (NormedSpace ℂ
    (A.ActualFiniteLogarithmicEulerSpace c →L[ℂ] A.ActualFiniteLogarithmicEulerSpace c))
local instance finiteLogRegularityCoefficientRealComplexComm :
    SMulCommClass ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c) where
  smul_comm r a f := by
    apply ContinuousLinearMap.ext
    intro p
    change (r : ℂ) • (a • f p) = a • ((r : ℂ) • f p)
    exact smul_comm _ _ _
local instance finiteLogRegularityCoefficientAddCommGroup :
    AddCommGroup (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.addCommGroup
local instance finiteLogRegularityFormAddCommGroup :
    AddCommGroup ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.addCommGroup
local instance (priority := 4500) finiteLogRegularityFormAdd :
    Add ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  (finiteLogRegularityFormAddCommGroup A c).toAdd
local instance finiteLogRegularityFormRealNormedSpace :
    NormedSpace ℝ ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.toNormedSpace
local instance finiteLogRegularityFormComplexNormedSpace :
    NormedSpace ℂ ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.toNormedSpace
local instance finiteLogRegularityCoefficientComplexContinuousSMul :
    ContinuousSMul ℂ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.continuousSMul
local instance finiteLogRegularityCoefficientRealContinuousSMul :
    ContinuousSMul ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) where
  continuous_smul := by
    have h : Continuous (fun p : ℝ × A.ActualFiniteLogarithmicEulerCoefficients c =>
        (p.1 : ℂ) • p.2) :=
      (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
    apply h.congr
    intro p
    apply ContinuousLinearMap.ext
    intro v
    rfl
local instance finiteLogRegularityFormRealContinuousSMul :
    ContinuousSMul ℝ ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.continuousSMul
local instance finiteLogRegularityFormComplexContinuousConstSMul :
    ContinuousConstSMul ℂ ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ContinuousLinearMap.continuousConstSMul
local instance finiteLogRegularityFormContinuousSMul :
    ContinuousSMul ℂ ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) where
  continuous_smul := by
    have h : Continuous (fun p : ℂ ×
        ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) =>
        p.1.re • p.2 + p.1.im • (Complex.I • p.2)) :=
      ((Complex.continuous_re.comp continuous_fst).smul continuous_snd).add
        ((Complex.continuous_im.comp continuous_fst).smul
          (continuous_snd.const_smul Complex.I))
    apply h.congr
    intro p
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (p.1.re : ℂ) • (p.2 u v) +
      (p.1.im : ℂ) • (Complex.I • (p.2 u v)) = p.1 • (p.2 u v)
    rw [smul_smul, ← add_smul, Complex.re_add_im]
local instance finiteLogRegularityFormScalarTower :
    IsScalarTower ℝ ℂ ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) where
  smul_assoc r a f := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro p
    change ((r : ℂ) * a) • f u p = (r : ℂ) • (a • f u p)
    exact mul_smul _ _ _

/-- The same original constant coefficient form before multiplication
by the original reciprocal equation. -/
def actualFiniteEulerLogarithmicConstantOneForm (H : ι) :
    (Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c :=
  ((ContinuousLinearMap.toSpanSingleton ℂ (A.actualFiniteLogarithmicGeneratorCoefficient c H)).restrictScalars ℝ).comp
    (A.actualNormalRealCLM H)

@[simp] theorem actualFiniteEulerLogarithmicConstantOneForm_apply
    (H : ι) (u : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicConstantOneForm c H u =
      A.normal H u • A.actualFiniteLogarithmicGeneratorCoefficient c H := rfl

/-- The actual original coefficient form is its actual finite weighted
sum of original constant forms. -/
theorem actualFiniteEulerLogarithmicOneForm_eq_weightedSum :
    A.actualFiniteEulerLogarithmicOneForm c = fun x =>
      ∑ H : ι, (logarithmicPeriodConstant⁻¹ * (A.normal H x - A.offset H)⁻¹) •
        A.actualFiniteEulerLogarithmicConstantOneForm c H := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  rw [actualFiniteEulerLogarithmicOneForm_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    actualFiniteEulerLogarithmicConstantOneForm_apply, smul_smul]

/-- Actual original inverse calculus proves infinite smoothness on the
actual original open complement. -/
theorem actualFiniteEulerLogarithmicOneForm_contDiffOn :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (A.actualFiniteEulerLogarithmicOneForm c)
      A.ambientComplementSet := by
  rw [actualFiniteEulerLogarithmicOneForm_eq_weightedSum]
  apply ContDiffOn.sum
  intro H _
  have hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => A.normal H x - A.offset H) A.ambientComplementSet := by
    simpa only [actualNormalRealCLM_apply] using
      ((A.actualNormalRealCLM H).contDiff.sub contDiff_const).contDiffOn
  have hne : ∀ x ∈ A.ambientComplementSet, A.normal H x - A.offset H ≠ 0 :=
    fun x hx => sub_ne_zero.mpr (hx H)
  have hc : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : Fin d → ℂ => logarithmicPeriodConstant⁻¹) A.ambientComplementSet :=
    contDiffOn_const
  exact (hc.mul (hf.inv hne)).smul_const
    (A.actualFiniteEulerLogarithmicConstantOneForm c H)

/-- The actual real derivative of the original normalized reciprocal equation. -/
def actualFiniteEulerLogarithmicScalarDerivative (H : ι) (x : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℝ] ℂ :=
  logarithmicPeriodConstant⁻¹ •
    ((-ContinuousLinearMap.mulLeftRight ℝ ℂ
      (A.normal H x - A.offset H)⁻¹ (A.normal H x - A.offset H)⁻¹).comp
        (A.actualNormalRealCLM H))

theorem actualFiniteEulerLogarithmicScalar_hasFDerivAt
    (H : ι) (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) :
    HasFDerivAt (fun y => logarithmicPeriodConstant⁻¹ * (A.normal H y - A.offset H)⁻¹)
      (A.actualFiniteEulerLogarithmicScalarDerivative H x) x := by
  have h := ((hasFDerivAt_inv' (𝕜 := ℝ) (sub_ne_zero.mpr (hx H))).comp x
    (A.actualAffineEquationFunction_hasFDerivAt H x)).const_mul logarithmicPeriodConstant⁻¹
  simpa only [actualAffineEquationFunction, actualFiniteEulerLogarithmicScalarDerivative] using h

/-- The same actual finite sum has this genuine original derivative. -/
def actualFiniteEulerLogarithmicOneFormDerivative (x : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℝ]
      ((Fin d → ℂ) →L[ℝ] A.ActualFiniteLogarithmicEulerCoefficients c) :=
  ∑ H : ι, (A.actualFiniteEulerLogarithmicScalarDerivative H x).smulRight
    (A.actualFiniteEulerLogarithmicConstantOneForm c H)

theorem actualFiniteEulerLogarithmicOneForm_hasFDerivAt
    (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) :
    HasFDerivAt (A.actualFiniteEulerLogarithmicOneForm c)
      (A.actualFiniteEulerLogarithmicOneFormDerivative c x) x := by
  rw [actualFiniteEulerLogarithmicOneForm_eq_weightedSum]
  simpa only [actualFiniteEulerLogarithmicOneFormDerivative] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun H _ =>
      (A.actualFiniteEulerLogarithmicScalar_hasFDerivAt H x hx).smul_const
        (A.actualFiniteEulerLogarithmicConstantOneForm c H)))

/-- The genuine inverse derivative is symmetric on the two genuine
original tangent vectors, before exterior alternation. -/
theorem actualFiniteEulerLogarithmicOneFormDerivative_symmetric
    (x : Fin d → ℂ) (u v : Fin d → ℂ) :
    A.actualFiniteEulerLogarithmicOneFormDerivative c x u v =
      A.actualFiniteEulerLogarithmicOneFormDerivative c x v u := by
  simp only [actualFiniteEulerLogarithmicOneFormDerivative, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro H _
  change (A.actualFiniteEulerLogarithmicScalarDerivative H x u) •
      (A.actualFiniteEulerLogarithmicConstantOneForm c H v) =
    (A.actualFiniteEulerLogarithmicScalarDerivative H x v) •
      (A.actualFiniteEulerLogarithmicConstantOneForm c H u)
  rw [actualFiniteEulerLogarithmicConstantOneForm_apply,
    actualFiniteEulerLogarithmicConstantOneForm_apply, smul_smul, smul_smul]
  apply congrArg (fun a : ℂ => a • A.actualFiniteLogarithmicGeneratorCoefficient c H)
  change (logarithmicPeriodConstant⁻¹ *
      (-((A.normal H x - A.offset H)⁻¹ * A.normal H u *
        (A.normal H x - A.offset H)⁻¹))) * A.normal H v =
    (logarithmicPeriodConstant⁻¹ *
      (-((A.normal H x - A.offset H)⁻¹ * A.normal H v *
        (A.normal H x - A.offset H)⁻¹))) * A.normal H u
  ring

/-- Native exterior differentiation of the actual original finite
coefficient form vanishes on the actual original complement. -/
theorem actualFiniteEulerLogarithmicOneForm_extDeriv_eq_zero
    (x : Fin d → ℂ) (hx : x ∈ A.ambientComplementSet) :
    extDeriv (fun y => ContinuousAlternatingMap.ofSubsingleton ℝ (Fin d → ℂ)
      (A.ActualFiniteLogarithmicEulerCoefficients c) (0 : Fin 1)
      (A.actualFiniteEulerLogarithmicOneForm c y)) x = 0 := by
  exact OpenSmoothForms.extDeriv_oneForm_eq_zero_of_symmetric_derivative
    (A.actualFiniteEulerLogarithmicOneForm c)
    (A.actualFiniteEulerLogarithmicOneFormDerivative c x) x
    (A.actualFiniteEulerLogarithmicOneForm_hasFDerivAt c x hx)
    (A.actualFiniteEulerLogarithmicOneFormDerivative_symmetric c x)

end ChenRanks.AffineArrangement
