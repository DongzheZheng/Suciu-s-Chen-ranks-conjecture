import ChenRanks.KoszulCanonicalFamilyGradingAdditiveParents

/-! The genuine unchanged left composite as its native additive map.
The function is the original reconstruction applied after the original
lmap; no additivity or grading property is an input. -/
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

local instance (priority := 5000) gradingLeftTargetAddZero :
    AddZero ((P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SharedCanonicalFamilyOriginalComponent k E I P) :=
  (gradingFunctionSharedTargetAddMonoid k E I).toAddZeroClass.toAddZero

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



/-- The actual native additive-map composite underlying the original left function. -/
def canonicalFamilyGradingLeftAddHom :=
  (canonicalFamilyHomogeneousDirectSumEquiv k E I hsep).toLinearMap.toAddMonoidHom.comp
    (DirectSum.lmap (originalCanonicalFamilyHomogeneousMap k E I b)).toAddMonoidHom


end ChenRanks.Koszul
