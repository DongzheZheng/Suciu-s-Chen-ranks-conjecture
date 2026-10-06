import ChenRanks.ArrangementFiniteEulerDevelopingAxis
import ChenRanks.DiscretePrincipalFrameLiftDerivative

/-! Genuine local differentiation of the actual arrangement's developing
axis along an actual continuous lifted curve.  The actual neighborhood,
local frame identity and local primitive derivative are all supplied by
the already constructed arrangement factories.  Only continuity of the
curve and the derivative of its actual original ambient projection are
intermediate path data; no local constancy or period is assumed.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison TopologicalComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance liftedAxisOriginalNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance liftedAxisOriginalNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance liftedAxisOriginalRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance liftedAxisOriginalScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance liftedAxisEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance liftedAxisQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance liftedAxisQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance liftedAxisQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) liftedAxisQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (liftedAxisQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) liftedAxisQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (liftedAxisQuotientRealModule A c).toSMul
local instance liftedAxisGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance liftedAxisGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- The actual ball at the actual projected lift point supplies every
local premise of the native differentiation theorem. -/
theorem actualFiniteEulerDevelopingAxis_lift_hasDerivAt
    (g : ℝ → A.ActualFiniteEulerPrincipalTotalSpace c) (t : ℝ)
    (hg : ContinuousAt g t) (u : Fin d → ℂ)
    (hu : HasDerivAt (fun z => ((g z).1 : A.Complement).val) u t) :
    HasDerivAt (fun z => A.actualFiniteEulerDevelopingAxis c (g z))
      (A.actualFiniteEulerAxisOperatorQuotient c
        (A.actualFiniteEulerLogarithmicOneForm c ((g t).1 : A.Complement).val u)) t := by
  let U := A.actualComplementBallAt ((g t).1 : A.Complement)
  have ht : (g t).1 ∈ (A.actualFiniteEulerPrincipalFrameCover c).baseSet U :=
    A.mem_actualComplementBallBaseSet_at ((g t).1 : A.Complement)
  exact discretePrincipalFrameLift_hasDerivAt
    (A.actualFiniteEulerPrincipalFrameCover c) (A.actualFiniteEulerAxisCharacter c)
    (fun x : A.Complement => x.val) g t hg U ht
    (A.actualFiniteEulerBallAxisPrimitive c U)
    (A.actualFiniteEulerBallFrame_axisCharacter_eq c U)
    ((A.actualFiniteEulerAxisOperatorQuotient c).comp
      (A.actualFiniteEulerLogarithmicOneForm c ((g t).1 : A.Complement).val))
    (A.actualFiniteEulerBallAxisPrimitive_derivative c U
      ((g t).1 : A.Complement).val ht) u hu

end ChenRanks.AffineArrangement
