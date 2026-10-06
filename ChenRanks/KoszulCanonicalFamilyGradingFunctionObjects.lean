import ChenRanks.KoszulCanonicalFamilyGradingStatement

/-! The two unchanged underlying functions in the actual canonical
family grading diagram. This file defines only those original functions
and their full equality, with no additivity or diagram premise. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

/- The original componentwise operation parents are projected directly
from the existing original target dictionary. No new operation is chosen. -/
local instance (priority := 4000) gradingFunctionTargetZero :
    Zero (CanonicalFamilyModule k E I) :=
  (canonicalFamilyTargetAddCommMonoid k E I).toZero

local instance (priority := 4000) gradingFunctionTargetAdd :
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

/-- The unchanged left underlying function of the full original diagram. -/
def canonicalFamilyGradingLeftFunction :
    (⨁ r, homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) → CanonicalFamilyModule k E I :=
  fun z => canonicalFamilyHomogeneousDirectSumEquiv k E I hsep
    (DirectSum.lmap (originalCanonicalFamilyHomogeneousMap k E I b) z)

/-- The unchanged right underlying function of the full original diagram. -/
def canonicalFamilyGradingRightFunction :
    (⨁ r, homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) → CanonicalFamilyModule k E I :=
  fun z => originalCanonicalFamilyBaseMap k E I
    (homogeneousDirectSumEquiv k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) z)

/-- The completely defined plain-function equality for the original
full diagram; no equality evidence is part of this definition. -/
def canonicalFamilyGradingFunctionDiagram : Prop :=
  canonicalFamilyGradingLeftFunction k E I b hsep =
    canonicalFamilyGradingRightFunction k E I b

end ChenRanks.Koszul
