import ChenRanks.OpenSmoothFiniteFlatParallelInverse
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiation of the actually constructed finite parallel inverse

The genuine finite polynomial inverse is differentiated with the native
noncommutative product rule.  Its already proved actual inverse identity
and the already proved actual parallel equation force its derivative to be
minus the inverse times the original coefficient form.  An inverse function,
an inverse-derivative equation and an inverse smoothness assumption are not
supplied as premises.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

variable {E R : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
variable [FiniteDimensional ℝ R]

variable (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
variable (ω : E → E →L[ℝ] R)
variable (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
variable (hclosed : ∀ x ∈ s, extDeriv (fun y =>
  ContinuousAlternatingMap.ofSubsingleton ℝ E R (0 : Fin 1) (ω y)) x = 0)
variable (hcomm : ∀ x ∈ s, ∀ u v : E, ω x u * ω x v = ω x v * ω x u)
variable (P : ℕ → Submodule ℝ R)
variable (hmul : ∀ a b : ℕ, ∀ r t : R, r ∈ P a → t ∈ P b → r * t ∈ P (a + b))
variable (hone : (1 : R) ∈ P 0)
variable (hωvalues : ∀ x ∈ s, ∀ v : E, ω x v ∈ P 1)
variable (x₀ : E)

/-- Every actual directional derivative of the explicit original inverse
is the negative of its actual left product with the original form. -/
theorem actualFiniteFlatParallelInverseFunction_fderiv_apply
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥)
    (x : E) (hx : x ∈ s) (v : E) :
    fderiv ℝ
      (actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ c) x v =
      -(actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ c x * ω x v) := by
  let U := actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  let V := actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  have hV : DifferentiableAt ℝ V x :=
    (((actualFiniteFlatParallelInverseFunction_smooth s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ c).differentiableOn (by simp)) x hx).differentiableAt
      (hso.mem_nhds hx)
  have hU := actualFiniteFlatParallelFunction_derivative s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c hbound x hx
  have hprod := hV.hasFDerivAt.mul' hU
  have hidentity : V * U = fun _ => (1 : R) := by
    funext y
    exact actualFiniteFlatParallelInverseFunction_mul_function
      s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound y
  rw [hidentity] at hprod
  have hz := congrArg (fun d : E →L[ℝ] R => d v)
    (hprod.unique (hasFDerivAt_const (1 : R) x))
  change V x * (ω x v * U x) + fderiv ℝ V x v * U x = 0 at hz
  have hd : fderiv ℝ V x v * U x = -(V x * (ω x v * U x)) :=
    add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using hz)
  have hUV : U x * V x = 1 :=
    actualFiniteFlatParallelFunction_mul_inverseFunction s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c hbound x
  change fderiv ℝ V x v = -(V x * ω x v)
  calc
    fderiv ℝ V x v = (fderiv ℝ V x v * U x) * V x := by
      rw [mul_assoc, hUV, mul_one]
    _ = -(V x * (ω x v * U x)) * V x := congrArg (fun r : R => r * V x) hd
    _ = -(V x * ω x v) := by
      simp only [neg_mul, mul_assoc, hUV, mul_one]

/-- The explicit finite inverse has its actual complete native derivative. -/
theorem actualFiniteFlatParallelInverseFunction_derivative
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥)
    (x : E) (hx : x ∈ s) :
    HasFDerivAt
      (actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ c)
      (-((ContinuousLinearMap.mul ℝ R)
        (actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
          P hmul hone hωvalues x₀ c x)).comp (ω x)) x := by
  let V := actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  have hV : DifferentiableAt ℝ V x :=
    (((actualFiniteFlatParallelInverseFunction_smooth s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ c).differentiableOn (by simp)) x hx).differentiableAt
      (hso.mem_nhds hx)
  have hd : fderiv ℝ V x = -((ContinuousLinearMap.mul ℝ R) (V x)).comp (ω x) := by
    ext v
    exact actualFiniteFlatParallelInverseFunction_fderiv_apply
      s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound x hx v
  exact hd ▸ hV.hasFDerivAt

end ChenRanks.OpenSmoothForms
