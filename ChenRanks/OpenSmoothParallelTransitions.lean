import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-! Genuine local parallel functions for the same actual coefficient
form have constant overlap transitions. The vanishing derivative follows
from the native noncommutative product rule, including its actual order.
Convexity and the native mean-value theorem prove constancy, so no locally
constant transition is supplied. Applications derive the two derivative
identities from their already constructed finite parallel functions.
-/
noncomputable section
namespace ChenRanks.OpenSmoothForms
variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedRing R] [NormedAlgebra ℝ R]
variable (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
variable (ω : E → E →L[ℝ] R) (V U : E → R)
variable (hV : ∀ x ∈ s, HasFDerivAt V
  (-((ContinuousLinearMap.mul ℝ R) (V x)).comp (ω x)) x)
variable (hU : ∀ x ∈ s, HasFDerivAt U
  (((ContinuousLinearMap.mul ℝ R).flip (U x)).comp (ω x)) x)

include hV hU in
/-- The actual overlap inverse-times-frame derivative is zero. -/
theorem parallelTransition_hasFDerivAt_zero (x : E) (hx : x ∈ s) :
    HasFDerivAt (fun y : E => V y * U y) (0 : E →L[ℝ] R) x := by
  have h := (hV x hx).mul' (hU x hx)
  convert h using 1
  ext v
  change (0 : R) = V x * (ω x v * U x) + (-(V x * ω x v)) * U x
  rw [neg_mul, mul_assoc, add_neg_cancel]

include hs hso hV hU in
/-- Native mean value proves true equality on a genuine convex overlap. -/
theorem parallelTransition_eq (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
    V x * U x = V y * U y := by
  have hd : DifferentiableOn ℝ (fun z => V z * U z) s := fun z hz =>
    (parallelTransition_hasFDerivAt_zero s ω V U hV hU z hz).differentiableAt.differentiableWithinAt
  have hf : ∀ z ∈ s, fderivWithin ℝ (fun z => V z * U z) s z = 0 := fun z hz =>
    (parallelTransition_hasFDerivAt_zero s ω V U hV hU z hz).hasFDerivWithinAt.fderivWithin
      (hso.uniqueDiffWithinAt hz)
  exact hs.is_const_of_fderivWithin_eq_zero hd hf hx hy

variable {H : Type*} [TopologicalSpace H]

include hs hso hV hU in
/-- An injective actual operator interpretation transfers proved constant
transitions to the genuine group-valued transitions, hence continuity
for its original topology, including the discrete topology. -/
theorem parallelTransition_discrete_continuousOn
    (ι : H → R) (hι : Function.Injective ι) (T : E → H)
    (hT : ∀ x ∈ s, ι (T x) = V x * U x) : ContinuousOn T s := by
  by_cases hsne : s.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hsne
    apply continuousOn_const.congr
    intro x hx
    apply hι
    rw [hT x hx, hT x₀ hx₀]
    exact parallelTransition_eq s hs hso ω V U hV hU x x₀ hx hx₀
  · have hempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hsne
    rw [hempty]
    exact continuousOn_empty T

end ChenRanks.OpenSmoothForms
