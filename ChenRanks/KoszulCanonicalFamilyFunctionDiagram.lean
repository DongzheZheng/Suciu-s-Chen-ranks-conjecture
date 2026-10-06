import ChenRanks.KoszulCanonicalFamilyFunctionInsertion
import ChenRanks.DirectSumAdditiveFunctionDiagram

/-! The unchanged original whole grading diagram is proved as an
equality of its actual functions. Native direct-sum induction uses only
the original maps' proved additivity and actual degree insertion rules.
The final linear-map equality is a separate thin extensional wrapper. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

local instance (priority := 5000) wholeFunctionTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetAddCommMonoid k E I

local instance (priority := 5000) wholeFunctionTargetZero :
    Zero (CanonicalFamilyModule k E I) :=
  (canonicalFamilyTargetAddCommMonoid k E I).toZero

local instance (priority := 5000) wholeFunctionTargetAdd :
    Add (CanonicalFamilyModule k E I) :=
  (canonicalFamilyTargetAddCommMonoid k E I).toAdd

attribute [local instance 2500]
  registeredNativeOriginalGroup registeredNativeOriginalMonoid
  registeredNativeOriginalBaseCoefficients
attribute [local instance 2000]
  registeredFamilyComponentGroups registeredFamilyComponentMonoids
  registeredFamilyComponentBaseCoefficients registeredFamilyTargetGroup
  registeredFamilyTargetMonoid registeredFamilyTargetBaseCoefficients
  registeredHomogeneousGroups registeredHomogeneousMonoids registeredHomogeneousCoefficients
  registeredFamilyDegreeGroups registeredFamilyDegreeMonoids registeredFamilyDegreeCoefficients
attribute [local instance 3500]
  sharedDegreeParents sharedDegreeCoefficients sharedOriginalParents sharedOriginalCoefficients

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

/-- The actual whole diagram follows from true insertion identities,
without comparing newly reconstructed linear-map scalar dictionaries. -/
theorem originalCanonicalFamilyHomogeneousDirectSum_functionDiagram :
    canonicalFamilyGradingFunctionDiagram k E I b hsep := by
  change canonicalFamilyGradingLeftFunction k E I b hsep =
    canonicalFamilyGradingRightFunction k E I b
  funext z
  induction z using DirectSum.induction_on with
  | zero =>
      exact (canonicalFamilyGradingLeftFunction_zero k E I b hsep).trans
        (canonicalFamilyGradingRightFunction_zero k E I b).symm
  | of r z =>
      exact canonicalFamilyGradingFunctions_insertion k E I b hsep r z
  | add x y hx hy =>
      calc
        _ = canonicalFamilyGradingLeftFunction k E I b hsep x +
            canonicalFamilyGradingLeftFunction k E I b hsep y :=
          canonicalFamilyGradingLeftFunction_add k E I b hsep x y
        _ = canonicalFamilyGradingRightFunction k E I b x +
            canonicalFamilyGradingRightFunction k E I b y := congrArg₂ (· + ·) hx hy
        _ = _ := (canonicalFamilyGradingRightFunction_add k E I b x y).symm

end ChenRanks.Koszul
