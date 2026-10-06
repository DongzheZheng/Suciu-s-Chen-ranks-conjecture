import ChenRanks.ArrangementFiniteEulerMeridianAngularLift
import ChenRanks.ArrangementSmoothMeridianPeriodFunctionals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The genuine first-term period of the actual lifted original meridian.

The actual projected coefficient form is a finite sum of the original
normalized logarithms with their original generator classes.  Every
summand is genuinely integrable.  The already computed actual diagonal
and off-diagonal meridian integrals give the actual generator class.
Native FTC on the genuinely constructed covering lift then identifies
this actual integral with its actual developing-axis endpoint difference.

No integral, endpoint, monodromy, winding comparison, or first-term
identity is supplied as an assumption.  Transport to the original
fundamental-group character is a subsequent statement.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open Complex MeasureTheory LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance meridianAxisPeriodLabelDecidableEq : DecidableEq ι := Classical.decEq ι

local instance meridianAxisPeriodOriginalNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianAxisPeriodOriginalNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianAxisPeriodOriginalRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianAxisPeriodOriginalScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance meridianAxisPeriodEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance meridianAxisPeriodQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianAxisPeriodQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianAxisPeriodQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) meridianAxisPeriodQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (meridianAxisPeriodQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) meridianAxisPeriodQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (meridianAxisPeriodQuotientRealModule A c).toSMul
local instance meridianAxisPeriodQuotientCompleteSpace :
    CompleteSpace (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFinite_completeSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianAxisPeriodQuotientScalarComm :
    SMulCommClass ℝ ℂ (A.ActualFiniteEulerAxisQuotient c) where
  smul_comm r a q := by
    change (r : ℂ) • (a • q) = a • ((r : ℂ) • q)
    exact smul_comm _ _ _
local instance meridianAxisPeriodGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance meridianAxisPeriodGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- The actual coefficient form, actual original tangent and actual
axis quotient determine the original vector-valued integrand. -/
def actualFiniteEulerMeridianAxisIntegrand
    (H : ι) (m : A.MeridianDisk H) (θ : ℝ) : A.ActualFiniteEulerAxisQuotient c :=
  A.actualFiniteEulerAxisOperatorQuotient c
    (A.actualFiniteEulerLogarithmicOneForm c
      (A.meridianDiskAngleAmbientMap H m θ)
      (deriv (circleMap 0 m.radius) θ • m.normalVector))

/-- The actual integrand is the finite sum of the actual original
normalized logarithmic pullbacks and their actual generator classes. -/
theorem actualFiniteEulerMeridianAxisIntegrand_eq_sum
    (H : ι) (m : A.MeridianDisk H) (θ : ℝ) :
    A.actualFiniteEulerMeridianAxisIntegrand c H m θ =
      ∑ K : ι, (logarithmicPeriodConstant⁻¹ *
        A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ) •
          A.actualFiniteEulerAxisGeneratorClass c K := by
  rw [actualFiniteEulerMeridianAxisIntegrand,
    A.actualFiniteEulerAxisOperatorQuotient_form_value c
      ⟨A.meridianDiskAngleAmbientMap H m θ,
        A.meridianDiskAngleAmbientMap_mem_complement H m θ⟩
      (deriv (circleMap 0 m.radius) θ • m.normalVector)]
  apply Finset.sum_congr rfl
  intro K _
  apply congrArg (fun a : ℂ => a • A.actualFiniteEulerAxisGeneratorClass c K)
  simp only [actualNormalizedNativeLogValue, actualSmoothMeridianIntegrand,
    actualSmoothLogarithmicForm_apply, mul_assoc]

/-- Every actual original summand is continuously evaluated on the actual
meridian, hence is genuinely Bochner integrable in the actual quotient. -/
theorem actualFiniteEulerMeridianAxisSummand_intervalIntegrable
    (H K : ι) (m : A.MeridianDisk H) :
    IntervalIntegrable (fun θ : ℝ => (logarithmicPeriodConstant⁻¹ *
      A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ) •
        A.actualFiniteEulerAxisGeneratorClass c K) volume 0 (2 * Real.pi) := by
  exact (continuous_const.mul
    (A.actualSmoothMeridianIntegrand_continuous H m (A.actualSmoothLogarithmicForm K))
      |>.smul continuous_const).intervalIntegrable _ _

/-- The actual finite sum is itself genuinely interval integrable. -/
theorem actualFiniteEulerMeridianAxisIntegrand_intervalIntegrable
    (H : ι) (m : A.MeridianDisk H) :
    IntervalIntegrable (A.actualFiniteEulerMeridianAxisIntegrand c H m)
      volume 0 (2 * Real.pi) := by
  have he : A.actualFiniteEulerMeridianAxisIntegrand c H m =
      fun θ => ∑ K : ι, (logarithmicPeriodConstant⁻¹ *
        A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ) •
          A.actualFiniteEulerAxisGeneratorClass c K := by
    funext θ
    exact A.actualFiniteEulerMeridianAxisIntegrand_eq_sum c H m θ
  rw [he]
  have hi := IntervalIntegrable.sum Finset.univ (fun K _ =>
    A.actualFiniteEulerMeridianAxisSummand_intervalIntegrable c H K m)
  have hsum : (∑ K : ι, fun θ : ℝ => (logarithmicPeriodConstant⁻¹ *
      A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ) •
        A.actualFiniteEulerAxisGeneratorClass c K) =
      (fun θ : ℝ => ∑ K : ι, (logarithmicPeriodConstant⁻¹ *
        A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ) •
          A.actualFiniteEulerAxisGeneratorClass c K) := by
    funext θ
    simp only [Finset.sum_apply]
  rw [hsum] at hi
  exact hi

/-- Genuine scalar meridian periods retain their actual normalization
factor; they are not assigned coordinate values. -/
theorem actualFiniteEulerMeridianAxisScalarIntegral
    (H K : ι) (m : A.MeridianDisk H) :
    (∫ θ : ℝ in 0..2 * Real.pi, logarithmicPeriodConstant⁻¹ *
      A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ) =
        if K = H then (1 : ℂ) else 0 := by
  classical
  let f : ℝ → ℂ := fun θ =>
    A.actualSmoothMeridianIntegrand H m (A.actualSmoothLogarithmicForm K) θ
  have h := intervalIntegral.integral_const_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume)
    logarithmicPeriodConstant⁻¹ f
  change (∫ θ : ℝ in 0..2 * Real.pi, logarithmicPeriodConstant⁻¹ * f θ) = _
  refine h.trans ?_
  change logarithmicPeriodConstant⁻¹ *
    A.actualSmoothMeridianPeriod H m (A.actualSmoothLogarithmicForm K) = _
  by_cases hKH : K = H
  · subst K
    rw [A.actualSmoothMeridianPeriod_same_logarithm H m,
      inv_mul_cancel₀ logarithmicPeriodConstant_ne_zero, if_pos rfl]
  · rw [A.actualSmoothMeridianPeriod_other_logarithm H K m hKH,
      mul_zero, if_neg hKH]

/-- The actual vector-valued integral is the original actual generator
class, by native integration of the actual finite logarithmic sum. -/
theorem actualFiniteEulerMeridianAxisIntegral_eq_generator
    (H : ι) (m : A.MeridianDisk H) :
    (∫ θ : ℝ in 0..2 * Real.pi, A.actualFiniteEulerMeridianAxisIntegrand c H m θ) =
      A.actualFiniteEulerAxisGeneratorClass c H := by
  classical
  simp_rw [A.actualFiniteEulerMeridianAxisIntegrand_eq_sum c H m]
  rw [intervalIntegral.integral_finset_sum (fun K _ =>
    A.actualFiniteEulerMeridianAxisSummand_intervalIntegrable c H K m)]
  calc
    _ = ∑ K : ι, (if K = H then (1 : ℂ) else 0) •
        A.actualFiniteEulerAxisGeneratorClass c K := by
      apply Finset.sum_congr rfl
      intro K _
      rw [intervalIntegral.integral_smul_const]
      exact congrArg (fun a : ℂ => a • A.actualFiniteEulerAxisGeneratorClass c K)
        (A.actualFiniteEulerMeridianAxisScalarIntegral H K m)
    _ = A.actualFiniteEulerAxisGeneratorClass c H := by simp

/-- The genuine developing-axis endpoint difference of the genuinely
constructed native covering lift is the genuine original generator class. -/
theorem actualFiniteEulerMeridianDevelopingAxis_endpoint_difference
    (H : ι) (m : A.MeridianDisk H) :
    A.actualFiniteEulerDevelopingAxis c
        (A.actualFiniteEulerMeridianAngularLift c H m (2 * Real.pi)) -
      A.actualFiniteEulerDevelopingAxis c
        (A.actualFiniteEulerMeridianAngularLift c H m 0) =
      A.actualFiniteEulerAxisGeneratorClass c H := by
  have ha : 0 ≤ 2 * Real.pi := (mul_pos (by norm_num) Real.pi_pos).le
  have hc : Continuous (fun θ : ℝ => A.actualFiniteEulerDevelopingAxis c
      (A.actualFiniteEulerMeridianAngularLift c H m θ)) :=
    (A.actualFiniteEulerDevelopingAxis_continuous c).comp
      (A.actualFiniteEulerMeridianAngularLift c H m).continuous
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha hc.continuousOn
    (fun θ hθ => A.actualFiniteEulerMeridianDevelopingAxis_hasDerivAt c H m θ hθ)
    (A.actualFiniteEulerMeridianAxisIntegrand_intervalIntegrable c H m)
  exact hi.symm.trans (A.actualFiniteEulerMeridianAxisIntegral_eq_generator c H m)

end ChenRanks.AffineArrangement
