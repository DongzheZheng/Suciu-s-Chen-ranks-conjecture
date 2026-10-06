import ChenRanks.OpenSmoothFiniteFlatParallelFunction
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The actual finite parallel function has an actual smooth finite inverse

The deviation of the genuine constructed function from the unit has
actual raising degree one.  Actual multiplication adds those degrees,
and the actual finite subspace bound proves its actual nilpotence.
The explicit finite geometric sum is therefore the actual two-sided
inverse.  Its infinite smoothness follows from the actual finite
polynomial expression.

Neither nilpotence, invertibility, a selected inverse nor a final
automorphism is supplied as an input.  This is still the explicit
generic filtered-algebra stage, prior to its actual Lie-bracket and
arrangement specializations.
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

include hmul hone in
/-- Genuine raising degree of every actual power, by actual product
containment rather than a nilpotence detector. -/
theorem powers_mem_filteredSubspace (N : R) (hN : N ∈ P 1) (n : ℕ) : N ^ n ∈ P n := by
  induction n with
  | zero => simpa only [pow_zero] using hone
  | succ n ih =>
    rw [pow_succ']
    have h := hmul 1 n N (N ^ n) hN ih
    simpa only [Nat.add_comm 1 n] using h

/-- Actual raising values and actual finite degree bound prove the
original function's true nilpotence, without assuming nilpotence. -/
theorem actualFiniteFlatParallelFunction_sub_one_pow_eq_zero
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) :
    (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x - 1) ^
      (c + 1) = 0 := by
  have h := powers_mem_filteredSubspace P hmul hone _
    (actualFiniteFlatParallelFunction_sub_one_mem s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c x) (c + 1)
  simpa only [hbound, Submodule.mem_bot] using h

/-- The actual finite polynomial inverse of the actual finite sum. -/
def actualFiniteFlatParallelInverseFunction (c : ℕ) : E → R :=
  fun x => ∑ n ∈ Finset.range (c + 1),
    (1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) ^ n

theorem actualFiniteFlatParallelInverseFunction_smooth (c : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c) s := by
  apply ContDiffOn.sum
  intro n hn
  exact (contDiffOn_const.sub
    (actualFiniteFlatParallelFunction_smooth s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ c)).pow n

private theorem actualFiniteFlatParallelFunction_one_sub_pow_eq_zero
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) :
    (1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) ^
      (c + 1) = 0 := by
  rw [show 1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x =
      -(actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x - 1) by abel,
    neg_pow,
    actualFiniteFlatParallelFunction_sub_one_pow_eq_zero s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c hbound x, mul_zero]

/-- The explicit finite inverse is a genuine original left inverse. -/
theorem actualFiniteFlatParallelInverseFunction_mul_function
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) :
    actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x *
      actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x = 1 := by
  have h := geom_sum_mul_neg
    (1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) (c + 1)
  rw [show 1 - (1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) =
      actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x by abel,
    actualFiniteFlatParallelFunction_one_sub_pow_eq_zero s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c hbound x, sub_zero] at h
  exact h

/-- The same explicit polynomial is a genuine original right inverse. -/
theorem actualFiniteFlatParallelFunction_mul_inverseFunction
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) :
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x *
      actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x = 1 := by
  have h := mul_neg_geom_sum
    (1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) (c + 1)
  rw [show 1 - (1 - actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) =
      actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x by abel,
    actualFiniteFlatParallelFunction_one_sub_pow_eq_zero s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c hbound x, sub_zero] at h
  exact h

/-- The actual parallel function is a unit with its actual explicitly
constructed finite inverse, not with an inverse supplied by a premise. -/
theorem actualFiniteFlatParallelFunction_isUnit
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (x : E) :
    IsUnit (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x) := by
  refine ⟨⟨_, actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c x,
    actualFiniteFlatParallelFunction_mul_inverseFunction s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound x,
    actualFiniteFlatParallelInverseFunction_mul_function s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound x⟩,
    rfl⟩

end ChenRanks.OpenSmoothForms
