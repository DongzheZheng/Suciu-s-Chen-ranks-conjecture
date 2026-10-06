import ChenRanks.OpenSmoothFilteredPrimitiveRecursion
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# The actual finite sum satisfies the actual parallel equation

The actual primitives in the actual raising subspaces are summed.
Their genuine derivative equations telescope.  The actual subspace bound
and actual multiplication law, rather than a supplied last-term equation,
kill the last original product.  This proves the actual parallel equation
for the original noncommutative algebra coefficients.

The filtered algebra is an explicit intermediate input.  Its actual
construction from the native finite affine graded flag is separate.
Invertibility and preservation of the Lie bracket are not inferred here
from the differential equation alone.
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

/-- The actual finite sum of the actual constructed anchored primitives. -/
def actualFiniteFlatParallelFunction (c : ℕ) : E → R :=
  fun x => ∑ n ∈ Finset.range (c + 1),
    actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n x

@[simp] theorem actualFiniteFlatParallelFunction_zero :
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ 0 =
      fun _ => 1 := by
  funext x
  simp only [actualFiniteFlatParallelFunction, Nat.zero_add, Finset.sum_range_one,
    actualFilteredFlatPrimitiveFunction_zero]

theorem actualFiniteFlatParallelFunction_succ (c : ℕ) :
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ (c + 1) =
      fun x => actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x +
        actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ (c + 1) x := by
  funext x
  exact Finset.sum_range_succ _ _

theorem actualFiniteFlatParallelFunction_smooth (c : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c) s := by
  apply ContDiffOn.sum
  intro n hn
  exact actualFilteredFlatPrimitiveFunction_smooth s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n

theorem actualFiniteFlatParallelFunction_anchor (c : ℕ) :
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x₀ = 1 := by
  unfold actualFiniteFlatParallelFunction
  rw [Finset.sum_range_succ']
  simp only [actualFilteredFlatPrimitiveFunction_succ_anchor,
    actualFilteredFlatPrimitiveFunction_zero, Finset.sum_const_zero, zero_add]

/-- Genuine differentiation of the original finite sum telescopes to
the original coefficient form times the actual shorter sum. -/
theorem actualFiniteFlatParallelFunction_derivative_shorter_sum
    (c : ℕ) (x : E) (hx : x ∈ s) :
    HasFDerivAt
      (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c)
      (rightProductOneForm ω
        (fun y => ∑ n ∈ Finset.range c,
          actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n y) x) x := by
  induction c with
  | zero =>
    have hz : rightProductOneForm ω (fun y => ∑ n ∈ Finset.range 0,
        actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n y) x = 0 := by
      ext v
      simp only [rightProductOneForm_apply, Finset.sum_range_zero, mul_zero,
        ContinuousLinearMap.zero_apply]
    rw [hz, actualFiniteFlatParallelFunction_zero]
    exact hasFDerivAt_const (1 : R) x
  | succ c ih =>
    have hnext := actualFilteredFlatPrimitiveFunction_succ_derivative
      s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x hx
    have h := ih.add hnext
    rw [actualFiniteFlatParallelFunction_succ]
    convert h using 1
    ext v
    simp only [rightProductOneForm_apply, ContinuousLinearMap.add_apply,
      Finset.sum_range_succ, mul_add]

/-- The actual bounded raising degree kills the genuine last product,
so the actual finite sum solves the actual original parallel equation. -/
theorem actualFiniteFlatParallelFunction_derivative
    (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) (hx : x ∈ s) :
    HasFDerivAt
      (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c)
      (rightProductOneForm ω
        (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c) x) x := by
  have h := actualFiniteFlatParallelFunction_derivative_shorter_sum
    s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x hx
  have he : rightProductOneForm ω
      (fun y => ∑ n ∈ Finset.range c,
        actualFilteredFlatPrimitiveFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ n y) x =
      rightProductOneForm ω
        (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c) x := by
    ext v
    simp only [rightProductOneForm_apply, actualFiniteFlatParallelFunction,
      Finset.sum_range_succ, mul_add,
      actualFilteredFlatPrimitiveFunction_last_product_eq_zero s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ c hbound x hx v, add_zero]
  rw [he] at h
  exact h

/-- The original finite sum differs from the genuine unit by an actual
degree-one raising element, by the actual antitone flag and actual values. -/
theorem actualFiniteFlatParallelFunction_sub_one_mem
    (hP : Antitone P) (c : ℕ) (x : E) :
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x - 1
      ∈ P 1 := by
  unfold actualFiniteFlatParallelFunction
  rw [Finset.sum_range_succ']
  simp only [actualFilteredFlatPrimitiveFunction_zero, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro n hn
  apply hP (Nat.le_add_left 1 n)
  exact actualFilteredFlatPrimitiveFunction_mem s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ (n + 1) x

end ChenRanks.OpenSmoothForms
