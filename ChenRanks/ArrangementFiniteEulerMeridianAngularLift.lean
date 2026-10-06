import ChenRanks.ArrangementFiniteEulerLiftedAxisDerivative
import ChenRanks.ArrangementLogarithmicMeridianPeriods
import ChenRanks.ScaledCoveringPathLift

/-! The original angular meridian and its genuinely constructed native lift.

The lifted curve is defined through the actual native covering factory,
with the actual identity fiber coordinate over the original meridian's
starting point.  Its ambient projection is the original angular meridian
on the real period interval, by the actual clamped parameter identity.
Consequently the genuine developing axis has exactly the normalized
original logarithmic derivative on the interior of that interval.

The period calculation by native FTC, and comparison of the endpoint
with the native monodromy character, are subsequent steps.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open Set Topology unitInterval LieComparison TopologicalComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance meridianLiftOriginalNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianLiftOriginalNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianLiftOriginalRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianLiftOriginalScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance meridianLiftEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance meridianLiftQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianLiftQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianLiftQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) meridianLiftQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (meridianLiftQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) meridianLiftQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (meridianLiftQuotientRealModule A c).toSMul
local instance meridianLiftGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance meridianLiftGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- The actual identity point of the actual original meridian fiber. -/
def actualFiniteEulerMeridianLiftStart (H : ι) (m : A.MeridianDisk H) :
    A.ActualFiniteEulerPrincipalTotalSpace c :=
  ⟨A.meridianDiskPathMap H m 0, (1 : A.ActualFiniteEulerExponentialGroup c)⟩

/-- The actual native path lift, with a genuine continuous real angular extension. -/
def actualFiniteEulerMeridianAngularLift (H : ι) (m : A.MeridianDisk H) :
    C(ℝ, A.ActualFiniteEulerPrincipalTotalSpace c) :=
  scaledCoveringPathLift (A.actualFiniteEulerPrincipalProjection_isCoveringMap c)
    (A.meridianDiskPathMap H m) (A.actualFiniteEulerMeridianLiftStart c H m) rfl
    (2 * Real.pi)

/-- The actual lifted projection is the same original angular meridian,
not a chosen equation coordinate or an assumed parametrization. -/
theorem actualFiniteEulerMeridianAngularLift_base
    (H : ι) (m : A.MeridianDisk H) (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    ((A.actualFiniteEulerMeridianAngularLift c H m θ).1 : A.Complement).val =
      A.meridianDiskAngleAmbientMap H m θ := by
  have ha : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hp := congrArg (fun x : A.Complement => x.val)
    (scaledCoveringPathLift_lifts
      (A.actualFiniteEulerPrincipalProjection_isCoveringMap c)
      (A.meridianDiskPathMap H m) (A.actualFiniteEulerMeridianLiftStart c H m) rfl
      (2 * Real.pi) θ)
  have he : (2 * Real.pi) *
      (scaledUnitIntervalParameter (2 * Real.pi) θ : ℝ) = θ := by
    rw [scaledUnitIntervalParameter_coe_of_mem (2 * Real.pi) ha θ hθ]
    exact (mul_comm _ _).trans (div_mul_cancel₀ θ ha.ne')
  calc
    ((A.actualFiniteEulerMeridianAngularLift c H m θ).1 : A.Complement).val =
        (A.meridianDiskPathMap H m
          (scaledUnitIntervalParameter (2 * Real.pi) θ)).val := hp
    _ = A.meridianDiskAngleAmbientMap H m
        ((2 * Real.pi) * (scaledUnitIntervalParameter (2 * Real.pi) θ : ℝ)) :=
      (A.meridianDiskAngleAmbientMap_eq_original_meridian H m _).symm
    _ = A.meridianDiskAngleAmbientMap H m θ := congrArg _ he

/-- Actual native differentiation on the genuine open angular interval.
The derivative of the actual ambient projection is proved using its
actual local equality with the original smooth meridian. -/
theorem actualFiniteEulerMeridianDevelopingAxis_hasDerivAt
    (H : ι) (m : A.MeridianDisk H) (θ : ℝ) (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt
      (fun t => A.actualFiniteEulerDevelopingAxis c
        (A.actualFiniteEulerMeridianAngularLift c H m t))
      (A.actualFiniteEulerAxisOperatorQuotient c
        (A.actualFiniteEulerLogarithmicOneForm c
          (A.meridianDiskAngleAmbientMap H m θ)
          (deriv (_root_.circleMap 0 m.radius) θ • m.normalVector))) θ := by
  have heq : (fun t =>
      ((A.actualFiniteEulerMeridianAngularLift c H m t).1 : A.Complement).val) =ᶠ[𝓝 θ]
      A.meridianDiskAngleAmbientMap H m := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    exact A.actualFiniteEulerMeridianAngularLift_base c H m t (mem_Icc_of_Ioo ht)
  have hbase := (A.meridianDiskAngleAmbientMap_hasDerivAt H m θ).congr_of_eventuallyEq heq
  have h := A.actualFiniteEulerDevelopingAxis_lift_hasDerivAt c
    (A.actualFiniteEulerMeridianAngularLift c H m) θ
    (A.actualFiniteEulerMeridianAngularLift c H m).continuous.continuousAt
    (deriv (_root_.circleMap 0 m.radius) θ • m.normalVector) hbase
  rw [A.actualFiniteEulerMeridianAngularLift_base c H m θ (mem_Icc_of_Ioo hθ)] at h
  exact h

end ChenRanks.AffineArrangement
