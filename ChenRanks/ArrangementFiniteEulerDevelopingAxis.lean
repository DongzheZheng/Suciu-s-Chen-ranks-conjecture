import ChenRanks.ArrangementFiniteEulerPrincipalCovering
import ChenRanks.ArrangementFiniteEulerAxisDerivative
import ChenRanks.DiscretePrincipalFrameDevelopingCharacter

/-! The actual finite Euler monodromy has an actual continuous developing
axis function on its genuine covering. On each genuine original ball,
the same function is the actual smooth axis primitive plus the character
of the genuine discrete fiber coordinate. All continuity and character
identities are derived from the constructed original parallel functions;
neither a period identity nor a first-term comparison is an input.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
open LieComparison OpenSmoothForms TopologicalComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance developingAxisNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance developingAxisNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance developingAxisRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance developingAxisScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance developingAxisEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance developingAxisQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance developingAxisQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance developingAxisQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) developingAxisQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (developingAxisQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) developingAxisQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (developingAxisQuotientRealModule A c).toSMul
local instance developingAxisQuotientScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteEulerAxisQuotient c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance developingAxisGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance developingAxisGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- The genuine original axis character on the genuine actual group. -/
def actualFiniteEulerAxisCharacter :
    A.ActualFiniteEulerExponentialGroup c →* Multiplicative (A.ActualFiniteEulerAxisQuotient c) :=
  nativeEulerAxisAbelianCharacter ℂ (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)
    c (A.actualFiniteLogarithmicComponent_above c)

/-- The actual original smooth axis primitive on a genuine original ball. -/
def actualFiniteEulerBallAxisPrimitive (U : A.ActualComplementBall) :=
  A.actualFiniteEulerParallelAxisPrimitive c (A.actualComplementBallSet U)
    (A.actualComplementBallSet_convex U) (A.actualComplementBallSet_isOpen U)
    (A.actualComplementBallSet_contained U) U.center

theorem actualFiniteEulerBallAxisPrimitive_derivative
    (U : A.ActualComplementBall) (x : Fin d → ℂ)
    (hx : x ∈ A.actualComplementBallSet U) :
    HasFDerivAt (A.actualFiniteEulerBallAxisPrimitive c U)
      ((A.actualFiniteEulerAxisOperatorQuotient c).comp
        (A.actualFiniteEulerLogarithmicOneForm c x)) x :=
  A.actualFiniteEulerParallelAxisPrimitive_derivative c
    (A.actualComplementBallSet U) (A.actualComplementBallSet_convex U)
    (A.actualComplementBallSet_isOpen U) (A.actualComplementBallSet_contained U)
    U.center (A.actualComplementBallSet_center U) x hx

/-- The original ball-frame character is the actual original primitive. -/
theorem actualFiniteEulerBallFrame_axisCharacter_eq
    (U : A.ActualComplementBall) (x : A.Complement)
    (hx : x ∈ A.actualComplementBallBaseSet U) :
    Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerBallFrame c U x)) =
      A.actualFiniteEulerBallAxisPrimitive c U x.val := by
  change x.val ∈ A.actualComplementBallSet U at hx
  rw [actualFiniteEulerBallFrame, dif_pos hx]
  exact (A.actualFiniteEulerParallelAxisPrimitive_eq_character c
    (A.actualComplementBallSet U) (A.actualComplementBallSet_convex U)
    (A.actualComplementBallSet_isOpen U) (A.actualComplementBallSet_contained U)
    U.center (A.actualComplementBallSet_center U) ⟨x.val, hx⟩).symm

/-- Actual local differentiation gives actual continuity of the true
ball-frame character in the original complement topology. -/
theorem actualFiniteEulerBallFrame_axisCharacter_continuousOn
    (U : A.ActualComplementBall) :
    ContinuousOn (fun x => Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerBallFrame c U x))) (A.actualComplementBallBaseSet U) := by
  have hp : ContinuousOn (A.actualFiniteEulerBallAxisPrimitive c U)
      (A.actualComplementBallSet U) := fun x hx =>
    (A.actualFiniteEulerBallAxisPrimitive_derivative c U x hx).continuousAt.continuousWithinAt
  have hcomp : ContinuousOn
      (fun x : A.Complement => A.actualFiniteEulerBallAxisPrimitive c U x.val)
      (A.actualComplementBallBaseSet U) :=
    hp.comp continuous_subtype_val.continuousOn (fun _ hx => hx)
  apply hcomp.congr
  intro x hx
  exact A.actualFiniteEulerBallFrame_axisCharacter_eq c U x hx

/-- The actual selected-frame-corrected function on the genuine covering. -/
def actualFiniteEulerDevelopingAxis :
    A.ActualFiniteEulerPrincipalTotalSpace c → A.ActualFiniteEulerAxisQuotient c :=
  discretePrincipalFrameDevelopingCharacter
    (A.actualFiniteEulerPrincipalFrameCover c) (A.actualFiniteEulerAxisCharacter c)

theorem actualFiniteEulerDevelopingAxis_continuous :
    Continuous (A.actualFiniteEulerDevelopingAxis c) :=
  discretePrincipalFrameDevelopingCharacter_continuous
    (A.actualFiniteEulerPrincipalFrameCover c) (A.actualFiniteEulerAxisCharacter c)
    (A.actualFiniteEulerBallFrame_axisCharacter_continuousOn c)

/-- The native character of original monodromy is the actual endpoint
difference; there is no winding or comparison condition. -/
theorem actualFiniteEulerDevelopingAxis_monodromy_difference
    (base : A.Complement) (g : FundamentalGroup A.Complement base) :
    Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerMonodromy c base g)) =
      A.actualFiniteEulerDevelopingAxis c
        ((A.actualFiniteEulerPrincipalProjection_isCoveringMap c).monodromy g.toPath
          ((discretePrincipalFrameFiberCoordinates
            (A.actualFiniteEulerPrincipalFrameCover c) base).symm 1)).val -
      A.actualFiniteEulerDevelopingAxis c
        ((discretePrincipalFrameFiberCoordinates
          (A.actualFiniteEulerPrincipalFrameCover c) base).symm 1).val :=
  discretePrincipalFrameDevelopingCharacter_monodromy_difference
    (A.actualFiniteEulerPrincipalFrameCover c) (A.actualFiniteEulerAxisCharacter c) base g

end ChenRanks.AffineArrangement
