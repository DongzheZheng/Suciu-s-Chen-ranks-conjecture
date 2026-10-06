import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.ProjIcc

/-! The native path lift with a genuine clamped real parameter.

The actual native projection onto the unit interval supplies a continuous
extension of a covering path lift to the whole real line.  For a positive
scale, this parameter is the original division by that scale on its real
closed interval.  The endpoint and lifting identities are consequences
of the original covering API; no lift or endpoint identity is supplied.
-/

noncomputable section

namespace ChenRanks.TopologicalComparison

open Set unitInterval

/-- The native clamped parameter, with its native continuous-map proof. -/
def scaledUnitIntervalParameter (a : ℝ) : C(ℝ, I) :=
  ⟨fun t => projIcc (0 : ℝ) 1 zero_le_one (t / a),
    continuous_projIcc.comp (continuous_id.div_const a)⟩

@[simp] theorem scaledUnitIntervalParameter_zero (a : ℝ) :
    scaledUnitIntervalParameter a 0 = 0 := by
  apply Subtype.ext
  simp only [scaledUnitIntervalParameter, ContinuousMap.coe_mk, zero_div, coe_projIcc]
  norm_num

theorem scaledUnitIntervalParameter_terminal (a : ℝ) (ha : a ≠ 0) :
    scaledUnitIntervalParameter a a = 1 := by
  apply Subtype.ext
  simp only [scaledUnitIntervalParameter, ContinuousMap.coe_mk, div_self ha, coe_projIcc]
  norm_num

/-- On the genuine positive-scale interval, the clamped parameter is
literally the original real quotient. -/
theorem scaledUnitIntervalParameter_coe_of_mem
    (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : t ∈ Icc 0 a) :
    (scaledUnitIntervalParameter a t : ℝ) = t / a := by
  have hlo : 0 ≤ t / a := div_nonneg ht.1 ha.le
  have hhi : t / a ≤ 1 := (div_le_one ha).mpr ht.2
  change max 0 (min 1 (t / a)) = t / a
  rw [min_eq_right hhi, max_eq_right hlo]

variable {B Z : Type*} [TopologicalSpace B] [TopologicalSpace Z]
variable {p : Z → B} (cov : IsCoveringMap p)
variable (γ : C(I, B)) (z : Z) (hz : γ 0 = p z)

/-- A genuine real-parameter continuous lift, constructed using the
actual native covering lift and the actual native clamped parameter. -/
def scaledCoveringPathLift (a : ℝ) : C(ℝ, Z) :=
  (cov.liftPath γ z hz).comp (scaledUnitIntervalParameter a)

theorem scaledCoveringPathLift_lifts (a t : ℝ) :
    p (scaledCoveringPathLift cov γ z hz a t) =
      γ (scaledUnitIntervalParameter a t) :=
  congrFun (cov.liftPath_lifts γ z hz) (scaledUnitIntervalParameter a t)

@[simp] theorem scaledCoveringPathLift_zero (a : ℝ) :
    scaledCoveringPathLift cov γ z hz a 0 = z := by
  change cov.liftPath γ z hz (scaledUnitIntervalParameter a 0) = z
  rw [scaledUnitIntervalParameter_zero, cov.liftPath_zero]

/-- The actual terminal value is the genuine native lifted endpoint. -/
theorem scaledCoveringPathLift_terminal (a : ℝ) (ha : a ≠ 0) :
    scaledCoveringPathLift cov γ z hz a a = cov.liftPath γ z hz 1 := by
  change cov.liftPath γ z hz (scaledUnitIntervalParameter a a) = _
  rw [scaledUnitIntervalParameter_terminal a ha]

end ChenRanks.TopologicalComparison
