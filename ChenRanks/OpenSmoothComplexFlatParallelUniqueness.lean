import ChenRanks.OpenSmoothFiniteFlatParallelInverseDifferential
import ChenRanks.FiniteDimensionalComplexLieBracket
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual uniqueness with complex-linear coefficients and real derivatives

The coefficient algebra is the original algebra of complex-linear continuous
endomorphisms of the original finite complex Lie space.  Differentiation is
real.  The native continuous restriction map converts actual operators for
real differentiation and leaves every application unchanged.  The genuinely
constructed finite inverse trivializes an arbitrary actual solution; the
native mean-value theorem then proves zero-anchored uniqueness.

The solution equation for the test function is the stated intermediate
uniqueness problem.  Neither an invertible parallel function nor a chosen
inverse or a uniqueness detector is supplied as an input.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

open ChenRanks.LieComparison

variable (L : Type*) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

local instance complexParallelNormedAddCommGroup : NormedAddCommGroup L :=
  nativeFiniteNormedAddCommGroup ℂ L
local instance complexParallelNormedSpace : NormedSpace ℂ L := nativeFiniteNormedSpace ℂ L
local instance complexParallelRealNormedSpace : NormedSpace ℝ L :=
  NormedSpace.restrictScalars ℝ ℂ L
local instance complexParallelCompleteSpace : CompleteSpace L :=
  nativeFinite_completeSpace ℂ L
local instance complexParallelScalarTower : IsScalarTower ℝ ℂ L where
  smul_assoc r c x := by
    change ((r : ℂ) * c) • x = (r : ℂ) • (c • x)
    exact mul_smul _ _ _
local instance complexParallelSMulCommClass : SMulCommClass ℂ ℝ L where
  smul_comm c r x := by
    change c • ((r : ℂ) • x) = (r : ℂ) • (c • x)
    exact smul_comm _ _ _
local instance complexParallelEndRealNormedAlgebra : NormedAlgebra ℝ (L →L[ℂ] L) :=
  NormedAlgebra.restrictScalars ℝ ℂ (L →L[ℂ] L)
local instance complexParallelEndRealFiniteDimensional :
    FiniteDimensional ℝ (L →L[ℂ] L) :=
  FiniteDimensional.trans ℝ ℂ (L →L[ℂ] L)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
variable (ω : E → E →L[ℝ] (L →L[ℂ] L))
variable (hω : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ω s)
variable (hclosed : ∀ x ∈ s, extDeriv (fun y =>
  ContinuousAlternatingMap.ofSubsingleton ℝ E (L →L[ℂ] L) (0 : Fin 1) (ω y)) x = 0)
variable (hcomm : ∀ x ∈ s, ∀ u v : E, ω x u * ω x v = ω x v * ω x u)
variable (P : ℕ → Submodule ℝ (L →L[ℂ] L))
variable (hmul : ∀ a b : ℕ, ∀ r t : L →L[ℂ] L,
  r ∈ P a → t ∈ P b → r * t ∈ P (a + b))
variable (hone : (1 : L →L[ℂ] L) ∈ P 0)
variable (hωvalues : ∀ x ∈ s, ∀ v : E, ω x v ∈ P 1)
variable (x₀ : E)

include hs hso hω hclosed hcomm hmul hone hωvalues in
/-- Genuine uniqueness for real differentiation and the actual original
complex-linear operator coefficients. -/
theorem actualComplexFiniteFlatParallel_zero_anchored_solution_eq_zero
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (hx₀ : x₀ ∈ s)
    (q : E → L)
    (hq : ∀ x ∈ s, HasFDerivAt q
      (((nativeComplexEndRestrictScalars L).comp (ω x)).flip (q x)) x)
    (hanchor : q x₀ = 0) (x : E) (hx : x ∈ s) : q x = 0 := by
  let U := actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  let VInv := actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  let A : (L →L[ℂ] L) →L[ℝ] (L →L[ℝ] L) :=
    nativeComplexEndRestrictScalars L
  let z : E → L := fun y => VInv y (q y)
  have hzderivative (y : E) (hy : y ∈ s) : HasFDerivAt z (0 : E →L[ℝ] L) y := by
    have hV := actualFiniteFlatParallelInverseFunction_derivative
      s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound y hy
    have h : HasFDerivAt z
        ((A (VInv y)).comp ((A.comp (ω y)).flip (q y)) +
          (A.comp (-((ContinuousLinearMap.mul ℝ (L →L[ℂ] L))
            (VInv y)).comp (ω y))).flip (q y)) y :=
      (A.hasFDerivAt.comp y hV).clm_apply (hq y hy)
    have he : (A (VInv y)).comp ((A.comp (ω y)).flip (q y)) +
        (A.comp (-((ContinuousLinearMap.mul ℝ (L →L[ℂ] L))
          (VInv y)).comp (ω y))).flip (q y) = 0 := by
      ext u
      change VInv y (ω y u (q y)) + -(VInv y (ω y u (q y))) = 0
      exact add_neg_cancel _
    rw [he] at h
    exact h
  have hzdiff : DifferentiableOn ℝ z s := fun y hy =>
    (hzderivative y hy).differentiableAt.differentiableWithinAt
  have hzfd : ∀ y ∈ s, fderivWithin ℝ z s y = 0 := fun y hy =>
    (hzderivative y hy).hasFDerivWithinAt.fderivWithin (hso.uniqueDiffWithinAt hy)
  have heq : z x = z x₀ := hs.is_const_of_fderivWithin_eq_zero hzdiff hzfd hx hx₀
  have hzx : z x = 0 := by
    rw [heq]
    change VInv x₀ (q x₀) = 0
    rw [hanchor, map_zero]
  have hUV : U x * VInv x = 1 :=
    actualFiniteFlatParallelFunction_mul_inverseFunction s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c hbound x
  calc
    q x = (U x * VInv x) (q x) := by rw [hUV]; rfl
    _ = U x (z x) := rfl
    _ = 0 := by rw [hzx, map_zero]

end ChenRanks.OpenSmoothForms
