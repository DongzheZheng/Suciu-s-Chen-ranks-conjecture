import ChenRanks.KoszulCanonicalFamilyGradingAdditiveParents

/-! The genuine unchanged right composite as its native additive map.
The original canonical map follows the original source reconstruction.
No equality or additivity assertion is supplied as a premise. -/
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

local instance (priority := 5000) gradingRightTargetAddZero :
    AddZero (CanonicalFamilyModule k E I) :=
  (gradingFunctionOriginalTargetAddMonoid k E I).toAddZeroClass.toAddZero

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
/-- The actual native additive-map composite underlying the original right function. -/
def canonicalFamilyGradingRightAddHom :=
  (originalCanonicalFamilyBaseMap k E I).toAddMonoidHom.comp
    (homogeneousDirectSumEquiv k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I)).toLinearMap.toAddMonoidHom


end ChenRanks.Koszul
