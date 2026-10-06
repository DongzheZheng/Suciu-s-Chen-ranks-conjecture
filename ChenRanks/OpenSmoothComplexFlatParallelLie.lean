import ChenRanks.OpenSmoothComplexFlatParallelUniqueness
import ChenRanks.FiniteDimensionalComplexLieBracket

/-!
# The actual finite parallel function preserves the actual original bracket

The coefficient endomorphisms in this intermediate theorem are required to
satisfy the original derivation identity.  This structural condition is later
supplied by the native affine adjoint derivations; bracket preservation of the
parallel function is not an input.  Native differentiation of its genuine
bracket defect gives the original parallel equation.  The proved uniqueness
theorem for the constructed finite inverse then kills the actual defect.

The original complex Lie algebra has its genuinely constructed complex
coordinate norm and completeness; differentiation is real and every
coefficient and the resulting Lie equivalence is complex linear.  No bounded bracket, selected automorphism or
monodromy comparison is assumed.
-/

noncomputable section

namespace ChenRanks.OpenSmoothForms

open ChenRanks.LieComparison

variable (L : Type*) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

local instance complexFlatLieNormedAddCommGroup : NormedAddCommGroup L :=
  nativeFiniteNormedAddCommGroup ℂ L
local instance complexFlatLieNormedSpace : NormedSpace ℂ L := nativeFiniteNormedSpace ℂ L
local instance complexFlatLieRealNormedSpace : NormedSpace ℝ L :=
  NormedSpace.restrictScalars ℝ ℂ L
local instance complexFlatLieCompleteSpace : CompleteSpace L :=
  nativeFinite_completeSpace ℂ L
local instance complexFlatLieScalarTower : IsScalarTower ℝ ℂ L where
  smul_assoc r c x := by
    change ((r : ℂ) * c) • x = (r : ℂ) • (c • x)
    exact mul_smul _ _ _
local instance complexFlatLieSMulCommClass : SMulCommClass ℂ ℝ L where
  smul_comm c r x := by
    change c • ((r : ℂ) • x) = (r : ℂ) • (c • x)
    exact smul_comm _ _ _
local instance complexFlatLieEndRealNormedAlgebra : NormedAlgebra ℝ (L →L[ℂ] L) :=
  NormedAlgebra.restrictScalars ℝ ℂ (L →L[ℂ] L)
local instance complexFlatLieEndRealFiniteDimensional : FiniteDimensional ℝ (L →L[ℂ] L) :=
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

/-- The native product rule gives the original parallel equation for
the actual bracket defect of the actually constructed finite sum. -/
theorem actualComplexFiniteFlatParallelLieDefect_derivative
    (c : ℕ) (hbound : P (c + 1) = ⊥)
    (hderivation : ∀ x ∈ s, ∀ (v : E) (a b : L),
      ω x v ⁅a, b⁆ = ⁅ω x v a, b⁆ + ⁅a, ω x v b⁆)
    (a b : L) (x : E) (hx : x ∈ s) :
    HasFDerivAt
      (fun y =>
        actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
          P hmul hone hωvalues x₀ c y ⁅a, b⁆ -
        ⁅actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
          P hmul hone hωvalues x₀ c y a,
          actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
            P hmul hone hωvalues x₀ c y b⁆)
      (((nativeComplexEndRestrictScalars L).comp (ω x)).flip
        (actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
          P hmul hone hωvalues x₀ c x ⁅a, b⁆ -
          ⁅actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
            P hmul hone hωvalues x₀ c x a,
            actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
              P hmul hone hωvalues x₀ c x b⁆)) x := by
  let U := actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  have hU := actualFiniteFlatParallelFunction_derivative s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c hbound x hx
  have heval (z : L) : HasFDerivAt (fun y => U y z)
      (((nativeComplexEndRestrictScalars L).comp (rightProductOneForm ω U x)).flip z) x := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      ((nativeComplexEndRestrictScalars L).hasFDerivAt.comp x hU).clm_apply
        (hasFDerivAt_const z x)
  have hbracket := nativeFiniteComplexLieBracket_hasFDerivAt L
    (fun y => U y a) (fun y => U y b)
    (((nativeComplexEndRestrictScalars L).comp (rightProductOneForm ω U x)).flip a)
    (((nativeComplexEndRestrictScalars L).comp (rightProductOneForm ω U x)).flip b) x (heval a) (heval b)
  have h := (heval ⁅a, b⁆).sub hbracket
  have he : ((nativeComplexEndRestrictScalars L).comp (rightProductOneForm ω U x)).flip ⁅a, b⁆ -
      ((nativeFiniteComplexLieRealBracket L (U x a)).comp
        (((nativeComplexEndRestrictScalars L).comp (rightProductOneForm ω U x)).flip b) +
        ((nativeFiniteComplexLieRealBracket L).comp
          (((nativeComplexEndRestrictScalars L).comp (rightProductOneForm ω U x)).flip a)).flip (U x b)) =
      ((nativeComplexEndRestrictScalars L).comp (ω x)).flip (U x ⁅a, b⁆ - ⁅U x a, U x b⁆) := by
    ext v
    change ω x v (U x ⁅a, b⁆) -
      (⁅U x a, ω x v (U x b)⁆ + ⁅ω x v (U x a), U x b⁆) =
      ω x v (U x ⁅a, b⁆ - ⁅U x a, U x b⁆)
    rw [map_sub, hderivation x hx v (U x a) (U x b)]
    abel
  rw [he] at h
  exact h

/-- The constructed finite parallel function genuinely preserves every
original bracket, without a bracket-preserving solution premise. -/
theorem actualComplexFiniteFlatParallelFunction_map_lie
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (hx₀ : x₀ ∈ s)
    (hderivation : ∀ x ∈ s, ∀ (v : E) (a b : L),
      ω x v ⁅a, b⁆ = ⁅ω x v a, b⁆ + ⁅a, ω x v b⁆)
    (a b : L) (x : E) (hx : x ∈ s) :
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ c x ⁅a, b⁆ =
      ⁅actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ c x a,
        actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
          P hmul hone hωvalues x₀ c x b⁆ := by
  let U := actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
    P hmul hone hωvalues x₀ c
  let q := fun y => U y ⁅a, b⁆ - ⁅U y a, U y b⁆
  have hanchor : q x₀ = 0 := by
    change U x₀ ⁅a, b⁆ - ⁅U x₀ a, U x₀ b⁆ = 0
    rw [show U x₀ = 1 from actualFiniteFlatParallelFunction_anchor
      s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ c]
    simp only [ContinuousLinearMap.one_apply, sub_self]
  have hzero := actualComplexFiniteFlatParallel_zero_anchored_solution_eq_zero
    L s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound hx₀ q
    (fun y hy => actualComplexFiniteFlatParallelLieDefect_derivative L s hs hso ω hω hclosed
      hcomm P hmul hone hωvalues x₀ c hbound hderivation a b y hy)
    hanchor x hx
  exact sub_eq_zero.mp hzero

/-- A genuine native Lie equivalence, constructed from the actual finite
parallel sum and its explicit finite polynomial inverse. -/
def actualComplexFiniteFlatParallelLieEquiv
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (hx₀ : x₀ ∈ s)
    (hderivation : ∀ x ∈ s, ∀ (v : E) (a b : L),
      ω x v ⁅a, b⁆ = ⁅ω x v a, b⁆ + ⁅a, ω x v b⁆)
    (x : E) (hx : x ∈ s) : L ≃ₗ⁅ℂ⁆ L := by
  let U : E → (L →L[ℂ] L) :=
    actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ c
  let V : E → (L →L[ℂ] L) :=
    actualFiniteFlatParallelInverseFunction s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ c
  exact {
    toFun := U x
    map_add' := (U x).map_add
    map_smul' := (U x).map_smul
    map_lie' := by
      intro a b
      exact actualComplexFiniteFlatParallelFunction_map_lie L s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ hP c hbound hx₀ hderivation a b x hx
    invFun := V x
    left_inv := by
      intro a
      have h := actualFiniteFlatParallelInverseFunction_mul_function
        s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound x
      exact congrArg (fun f : L →L[ℂ] L => f a) h
    right_inv := by
      intro a
      have h := actualFiniteFlatParallelFunction_mul_inverseFunction
        s hs hso ω hω hclosed hcomm P hmul hone hωvalues x₀ hP c hbound x
      exact congrArg (fun f : L →L[ℂ] L => f a) h }

/-- The native Lie equivalence has exactly the constructed original map. -/
theorem actualComplexFiniteFlatParallelLieEquiv_apply
    (hP : Antitone P) (c : ℕ) (hbound : P (c + 1) = ⊥) (hx₀ : x₀ ∈ s)
    (hderivation : ∀ x ∈ s, ∀ (v : E) (a b : L),
      ω x v ⁅a, b⁆ = ⁅ω x v a, b⁆ + ⁅a, ω x v b⁆)
    (x : E) (hx : x ∈ s) (a : L) :
    actualComplexFiniteFlatParallelLieEquiv L s hs hso ω hω hclosed hcomm
      P hmul hone hωvalues x₀ hP c hbound hx₀ hderivation x hx a =
      actualFiniteFlatParallelFunction s hs hso ω hω hclosed hcomm
        P hmul hone hωvalues x₀ c x a := rfl

end ChenRanks.OpenSmoothForms
