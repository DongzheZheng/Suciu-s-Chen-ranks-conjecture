import ChenRanks.ArrangementFiniteEulerMeridianAxisPeriod
import ChenRanks.CoveringPathLiftEndpoint

/-! The actual finite monodromy character on the original geometric meridian.

The original meridian is an actual loop at its actual original geometric
basepoint. Native monodromy and the genuinely constructed angular lift
have the same actual endpoint because they use the same native path
lift. The already proved actual FTC endpoint difference therefore gives
the original generator class. No period or monodromy identity is an input.

Transport to a different original basepoint and scalar character
comparison are subsequent statements.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison TopologicalComparison unitInterval

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance meridianMonodromyOriginalNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianMonodromyOriginalNormedSpace :
    NormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianMonodromyOriginalRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteLogarithmicEulerSpace c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c)
local instance meridianMonodromyOriginalScalarTower :
    IsScalarTower ℝ ℂ (A.ActualFiniteLogarithmicEulerSpace c) where
  smul_assoc r a p := by
    change ((r : ℂ) * a) • p = (r : ℂ) • (a • p)
    exact mul_smul _ _ _
local instance meridianMonodromyEndRealNormedAlgebra :
    NormedAlgebra ℝ (A.ActualFiniteLogarithmicEulerCoefficients c) :=
  NormedAlgebra.restrictScalars ℝ ℂ (A.ActualFiniteLogarithmicEulerCoefficients c)
local instance meridianMonodromyQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianMonodromyQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance meridianMonodromyQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) meridianMonodromyQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (meridianMonodromyQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) meridianMonodromyQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (meridianMonodromyQuotientRealModule A c).toSMul
local instance meridianMonodromyGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance meridianMonodromyGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- The original actual meridian as a genuine native loop. -/
def actualFiniteEulerMeridianLoop (H : ι) (m : A.MeridianDisk H) :
    Path (A.meridianDiskPathMap H m 0) (A.meridianDiskPathMap H m 0) :=
  ⟨A.meridianDiskPathMap H m, rfl, (A.meridianDiskPathMap_endpoints H m).symm⟩

/-- Its genuine class in the original fundamental group at its original
geometric basepoint. -/
def actualFiniteEulerMeridianFundamentalElement (H : ι) (m : A.MeridianDisk H) :
    FundamentalGroup A.Complement (A.meridianDiskPathMap H m 0) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (A.actualFiniteEulerMeridianLoop H m))

/-- The native identity-coordinate fiber point is the same original
identity-coordinate point used to define the actual angular lift. -/
theorem actualFiniteEulerMeridian_identityFiberPoint
    (H : ι) (m : A.MeridianDisk H) :
    ((discretePrincipalFrameFiberCoordinates
      (A.actualFiniteEulerPrincipalFrameCover c) (A.meridianDiskPathMap H m 0)).symm 1).val =
      A.actualFiniteEulerMeridianLiftStart c H m := rfl

/-- Native monodromy and the original angular lift use the same genuine
native path lift, so their actual endpoints agree. -/
theorem actualFiniteEulerMeridianMonodromy_endpoint
    (H : ι) (m : A.MeridianDisk H) :
    ((A.actualFiniteEulerPrincipalProjection_isCoveringMap c).monodromy
      (A.actualFiniteEulerMeridianFundamentalElement H m).toPath
      ((discretePrincipalFrameFiberCoordinates
        (A.actualFiniteEulerPrincipalFrameCover c) (A.meridianDiskPathMap H m 0)).symm 1)).val =
      A.actualFiniteEulerMeridianAngularLift c H m (2 * Real.pi) := by
  have ha : 2 * Real.pi ≠ 0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  rw [actualFiniteEulerMeridianAngularLift, scaledCoveringPathLift_terminal _ _ _ _ _ ha]
  exact coveringMonodromy_pathClass_val
    (A.actualFiniteEulerPrincipalProjection_isCoveringMap c)
    (A.actualFiniteEulerMeridianLoop H m) _

/-- The actual original monodromy character of the actual original
positive meridian is its actual original generator class. -/
theorem actualFiniteEulerAxisCharacter_meridian
    (H : ι) (m : A.MeridianDisk H) :
    Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerMonodromy c (A.meridianDiskPathMap H m 0)
        (A.actualFiniteEulerMeridianFundamentalElement H m))) =
      A.actualFiniteEulerAxisGeneratorClass c H := by
  have hm := A.actualFiniteEulerDevelopingAxis_monodromy_difference c
    (A.meridianDiskPathMap H m 0) (A.actualFiniteEulerMeridianFundamentalElement H m)
  rw [A.actualFiniteEulerMeridianMonodromy_endpoint c H m,
    A.actualFiniteEulerMeridian_identityFiberPoint c H m] at hm
  have hzero : A.actualFiniteEulerMeridianAngularLift c H m 0 =
      A.actualFiniteEulerMeridianLiftStart c H m :=
    scaledCoveringPathLift_zero _ _ _ _ _
  let ψ : A.ActualFiniteEulerPrincipalTotalSpace c →
      A.ActualFiniteEulerAxisQuotient c := A.actualFiniteEulerDevelopingAxis c
  have hstart := congrArg ψ hzero
  have hdiff := congrArg
    (fun z : A.ActualFiniteEulerAxisQuotient c =>
      ψ (A.actualFiniteEulerMeridianAngularLift c H m (2 * Real.pi)) - z)
    hstart.symm
  exact hm.trans (hdiff.trans
    (A.actualFiniteEulerMeridianDevelopingAxis_endpoint_difference c H m))

end ChenRanks.AffineArrangement
