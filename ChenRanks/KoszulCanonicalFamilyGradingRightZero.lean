import ChenRanks.KoszulCanonicalFamilyGradingRightAddHom
import ChenRanks.SharedExactTactic

/-! One complete original function equation, derived from the actual
native additive-map composite. The equality cache contains exactly the
unchanged original function formula, with no proof premise. -/
set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

/- Reuse the very same original target operation parents stored in the
unchanged function objects; no second operation dictionary is built. -/
attribute [local instance 4000] gradingFunctionTargetZero gradingFunctionTargetAdd
attribute [local instance 4500]
  gradingFunctionSharedTargetAddMonoid gradingFunctionOriginalTargetAddMonoid
attribute [local instance 5000] gradingRightTargetAddZero

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



omit [CharZero k] in
/-- The actual native composite proves the full original zero formula. -/
theorem canonicalFamilyGradingRightFunction_zero :
    canonicalFamilyGradingRightZeroEquation k E I b := by
  exact_shared_native (canonicalFamilyGradingRightAddHom k E I b).map_zero


end ChenRanks.Koszul
