import ChenRanks.ArrangementComplementBallCover
import ChenRanks.ArrangementFiniteEulerExponentialFrames
import ChenRanks.ArrangementFiniteEulerParallelInverseDerivative
import ChenRanks.OpenSmoothParallelTransitions
import ChenRanks.DiscretePrincipalFrameCovering

/-! Actual finite monodromy of the original arrangement complement.

The original complement's actual open balls and the genuinely constructed
finite parallel functions define the local frames. Their transition
functions are proved constant by the native product rule and mean value
theorem. The resulting native glued total space is a covering; its native
path lifts give a homomorphism of the original fundamental group.

No cover, selected local frame, transition constancy, flatness, path-lift
invariance or monodromy representation is supplied as an assumption.
Identification of its first term with the original meridian characters
and the higher leading-term comparison are subsequent theorems.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
open LieComparison OpenSmoothForms TopologicalComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance finiteCoverNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteCoverNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteCoverRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance finiteCoverScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance finiteCoverSMulCommClass :
    SMulCommClass ℂ ℝ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_comm a r p := by
    change a • ((r : ℂ) • p) = (r : ℂ) • (a • p)
    exact smul_comm _ _ _
local instance finiteCoverEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)

/-- The genuine exponential group is given the discrete topology for
the actual principal covering, leaving the original base topology intact. -/
local instance finiteCoverGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance finiteCoverGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- The actual parallel function on the actual original ambient ball. -/
def actualFiniteEulerBallParallel (U : A.ActualComplementBall) :=
  A.actualFiniteEulerParallelFunction c (A.actualComplementBallSet U)
    (A.actualComplementBallSet_convex U) (A.actualComplementBallSet_isOpen U)
    (A.actualComplementBallSet_contained U) U.center

/-- Its genuine polynomial inverse on the same actual original ball. -/
def actualFiniteEulerBallInverse (U : A.ActualComplementBall) :=
  A.actualFiniteEulerParallelInverse c (A.actualComplementBallSet U)
    (A.actualComplementBallSet_convex U) (A.actualComplementBallSet_isOpen U)
    (A.actualComplementBallSet_contained U) U.center

/-- A total local frame function whose values on its actual chart are
the actual constructed native exponential frames. -/
def actualFiniteEulerBallFrame (U : A.ActualComplementBall)
    (x : A.Complement) : A.ActualFiniteEulerExponentialGroup c := by
  classical
  exact if hx : x.val ∈ A.actualComplementBallSet U then
    A.actualFiniteEulerExponentialFrame c (A.actualComplementBallSet U)
      (A.actualComplementBallSet_convex U) (A.actualComplementBallSet_isOpen U)
      (A.actualComplementBallSet_contained U) U.center
      (A.actualComplementBallSet_center U) ⟨x.val, hx⟩
  else 1

theorem actualFiniteEulerBallFrameEnd_eq (U : A.ActualComplementBall)
    (x : A.Complement) (hx : x ∈ A.actualComplementBallBaseSet U) :
    A.actualFiniteEulerExponentialEnd c (A.actualFiniteEulerBallFrame c U x) =
      A.actualFiniteEulerBallParallel c U x.val := by
  change x.val ∈ A.actualComplementBallSet U at hx
  rw [actualFiniteEulerBallFrame, dif_pos hx]
  exact A.actualFiniteEulerExponentialFrameEnd_eq_parallel c
    (A.actualComplementBallSet U) (A.actualComplementBallSet_convex U)
    (A.actualComplementBallSet_isOpen U) (A.actualComplementBallSet_contained U)
    U.center (A.actualComplementBallSet_center U) ⟨x.val, hx⟩

/-- The chart actually chosen at an original point is anchored there. -/
theorem actualFiniteEulerBallFrame_at_self (x : A.Complement) :
    A.actualFiniteEulerBallFrame c (A.actualComplementBallAt x) x = 1 := by
  have hx := A.mem_actualComplementBallBaseSet_at x
  change x.val ∈ A.actualComplementBallSet (A.actualComplementBallAt x) at hx
  rw [actualFiniteEulerBallFrame, dif_pos hx]
  exact A.actualFiniteEulerExponentialFrame_anchor c
    (A.actualComplementBallSet (A.actualComplementBallAt x))
    (A.actualComplementBallSet_convex (A.actualComplementBallAt x))
    (A.actualComplementBallSet_isOpen (A.actualComplementBallAt x))
    (A.actualComplementBallSet_contained (A.actualComplementBallAt x))
    x.val (A.actualComplementBallSet_center (A.actualComplementBallAt x))

/-- Literal original product identity on the same actual exponential action. -/
theorem actualFiniteEulerCoverEnd_mul
    (h g : A.ActualFiniteEulerExponentialGroup c) :
    A.actualFiniteEulerExponentialEnd c (h * g) =
      A.actualFiniteEulerExponentialEnd c h * A.actualFiniteEulerExponentialEnd c g := by
  apply ContinuousLinearMap.ext
  intro p
  rfl

theorem actualFiniteEulerCoverEnd_one :
    A.actualFiniteEulerExponentialEnd c 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro p
  rfl

/-- The inverse group frame acts by the genuine original polynomial inverse. -/
theorem actualFiniteEulerBallFrameInvEnd_eq (U : A.ActualComplementBall)
    (x : A.Complement) (hx : x ∈ A.actualComplementBallBaseSet U) :
    A.actualFiniteEulerExponentialEnd c ((A.actualFiniteEulerBallFrame c U x)⁻¹) =
      A.actualFiniteEulerBallInverse c U x.val := by
  let h := A.actualFiniteEulerBallFrame c U x
  let u := A.actualFiniteEulerBallParallel c U x.val
  let v := A.actualFiniteEulerBallInverse c U x.val
  have he : A.actualFiniteEulerExponentialEnd c h = u :=
    A.actualFiniteEulerBallFrameEnd_eq c U x hx
  have huv : u * v = 1 :=
    A.actualFiniteEulerParallelFunction_mul_inverse c (A.actualComplementBallSet U)
      (A.actualComplementBallSet_convex U) (A.actualComplementBallSet_isOpen U)
      (A.actualComplementBallSet_contained U) U.center x.val
  have hinv : A.actualFiniteEulerExponentialEnd c h⁻¹ * u = 1 := by
    rw [← he, ← A.actualFiniteEulerCoverEnd_mul c,
      inv_mul_cancel, A.actualFiniteEulerCoverEnd_one c]
  calc
    A.actualFiniteEulerExponentialEnd c h⁻¹ =
        A.actualFiniteEulerExponentialEnd c h⁻¹ * (u * v) := by rw [huv, mul_one]
    _ = v := by rw [← mul_assoc, hinv, one_mul]

/-- The literal original product has the actual parallel interpretation
on each original overlap point; no large rewrite search is needed. -/
theorem actualFiniteEulerBallFrameProductEnd_eq
    (U V : A.ActualComplementBall) (x : A.Complement)
    (hx : x ∈ A.actualComplementBallBaseSet U ∩ A.actualComplementBallBaseSet V) :
    A.actualFiniteEulerExponentialEnd c
        ((A.actualFiniteEulerBallFrame c V x)⁻¹ * A.actualFiniteEulerBallFrame c U x) =
      A.actualFiniteEulerBallInverse c V x.val * A.actualFiniteEulerBallParallel c U x.val := by
  exact (A.actualFiniteEulerCoverEnd_mul c
    (A.actualFiniteEulerBallFrame c V x)⁻¹ (A.actualFiniteEulerBallFrame c U x)).trans
      (congrArg₂ (fun a b : A.ActualFiniteLogarithmicEulerCoefficients c => a * b)
        (A.actualFiniteEulerBallFrameInvEnd_eq c V x hx.2)
        (A.actualFiniteEulerBallFrameEnd_eq c U x hx.1))

/-- The actual original ambient parallel transitions are constant on
actual convex intersections, by the already proved derivative identities. -/
theorem actualFiniteEulerBallParallelTransition_eq
    (U V : A.ActualComplementBall) (x y : Fin d → ℂ)
    (hx : x ∈ A.actualComplementBallSet U ∩ A.actualComplementBallSet V)
    (hy : y ∈ A.actualComplementBallSet U ∩ A.actualComplementBallSet V) :
    A.actualFiniteEulerBallInverse c V x * A.actualFiniteEulerBallParallel c U x =
      A.actualFiniteEulerBallInverse c V y * A.actualFiniteEulerBallParallel c U y := by
  apply parallelTransition_eq
    (A.actualComplementBallSet U ∩ A.actualComplementBallSet V)
    ((A.actualComplementBallSet_convex U).inter (A.actualComplementBallSet_convex V))
    ((A.actualComplementBallSet_isOpen U).inter (A.actualComplementBallSet_isOpen V))
    (A.actualFiniteEulerLogarithmicOneForm c)
    (A.actualFiniteEulerBallInverse c V) (A.actualFiniteEulerBallParallel c U)
    (fun z hz => A.actualFiniteEulerParallelInverse_derivative c
      (A.actualComplementBallSet V) (A.actualComplementBallSet_convex V)
      (A.actualComplementBallSet_isOpen V) (A.actualComplementBallSet_contained V)
      V.center z hz.2)
    (fun z hz => A.actualFiniteEulerParallelFunction_derivative c
      (A.actualComplementBallSet U) (A.actualComplementBallSet_convex U)
      (A.actualComplementBallSet_isOpen U) (A.actualComplementBallSet_contained U)
      U.center z hz.1)
    x y hx hy

/-- Actual frame changes are constant on each genuine convex overlap. -/
theorem actualFiniteEulerBallFrameTransition_eq
    (U V : A.ActualComplementBall) (x y : A.Complement)
    (hx : x ∈ A.actualComplementBallBaseSet U ∩ A.actualComplementBallBaseSet V)
    (hy : y ∈ A.actualComplementBallBaseSet U ∩ A.actualComplementBallBaseSet V) :
    (A.actualFiniteEulerBallFrame c V x)⁻¹ * A.actualFiniteEulerBallFrame c U x =
      (A.actualFiniteEulerBallFrame c V y)⁻¹ * A.actualFiniteEulerBallFrame c U y := by
  apply A.actualFiniteEulerExponentialEnd_injective c
  exact (A.actualFiniteEulerBallFrameProductEnd_eq c U V x hx).trans
    ((A.actualFiniteEulerBallParallelTransition_eq c U V x.val y.val hx hy).trans
      (A.actualFiniteEulerBallFrameProductEnd_eq c U V y hy).symm)

/-- Proved constancy gives genuine discrete continuity, without assuming
individual frames are continuous for the discrete group topology. -/
theorem actualFiniteEulerBallFrameTransition_continuousOn
    (U V : A.ActualComplementBall) :
    ContinuousOn (fun x => (A.actualFiniteEulerBallFrame c V x)⁻¹ *
      A.actualFiniteEulerBallFrame c U x)
      (A.actualComplementBallBaseSet U ∩ A.actualComplementBallBaseSet V) := by
  by_cases hne : (A.actualComplementBallBaseSet U ∩ A.actualComplementBallBaseSet V).Nonempty
  · obtain ⟨y, hy⟩ := hne
    apply continuousOn_const.congr
    intro x hx
    exact A.actualFiniteEulerBallFrameTransition_eq c U V x y hx hy
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact continuousOn_empty _

/-- The actual original complement, actual balls and actual constructed
frames satisfy all native principal-cover data as a theorem. -/
def actualFiniteEulerPrincipalFrameCover :
    DiscretePrincipalFrameCover (ι := A.ActualComplementBall)
      (B := A.Complement) (H := A.ActualFiniteEulerExponentialGroup c) where
  baseSet := A.actualComplementBallBaseSet
  isOpen_baseSet := A.actualComplementBallBaseSet_isOpen
  indexAt := A.actualComplementBallAt
  mem_baseSet_at := A.mem_actualComplementBallBaseSet_at
  frame := A.actualFiniteEulerBallFrame c
  continuousOn_transition := A.actualFiniteEulerBallFrameTransition_continuousOn c

abbrev ActualFiniteEulerPrincipalTotalSpace :=
  DiscretePrincipalFrameTotalSpace (A.actualFiniteEulerPrincipalFrameCover c)

/-- The genuine native projection of the original glued total space. -/
def actualFiniteEulerPrincipalProjection :
    A.ActualFiniteEulerPrincipalTotalSpace c → A.Complement :=
  discretePrincipalFrameProjection (A.actualFiniteEulerPrincipalFrameCover c)

theorem actualFiniteEulerPrincipalProjection_isCoveringMap :
    IsCoveringMap (A.actualFiniteEulerPrincipalProjection c) :=
  discretePrincipalFrame_isCoveringMap (A.actualFiniteEulerPrincipalFrameCover c)

/-- Actual finite monodromy of the original native fundamental group.
There is no representation, lift or homotopy premise. -/
def actualFiniteEulerMonodromy (base : A.Complement) :
    FundamentalGroup A.Complement base →* A.ActualFiniteEulerExponentialGroup c :=
  discretePrincipalFrameMonodromy (A.actualFiniteEulerPrincipalFrameCover c) base

end ChenRanks.AffineArrangement
