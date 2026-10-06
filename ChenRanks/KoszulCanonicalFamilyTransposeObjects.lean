import ChenRanks.KoszulCanonicalFamilyNativeEvaluation

/-! The genuine native transpose object, separated from its computation
theorem. It retains the same original homogeneous quotient dictionaries. -/

set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

attribute [local instance 2500]
  registeredNativeOriginalGroup registeredNativeOriginalMonoid
  registeredNativeOriginalBaseCoefficients

attribute [local instance 2000]
  registeredFamilyComponentGroups registeredFamilyComponentMonoids
  registeredFamilyComponentBaseCoefficients registeredFamilyTargetGroup
  registeredFamilyTargetMonoid registeredFamilyTargetBaseCoefficients

attribute [local instance 3000]
  registeredHomogeneousGroups registeredHomogeneousMonoids registeredHomogeneousCoefficients
  registeredFamilyDegreeGroups registeredFamilyDegreeMonoids registeredFamilyDegreeCoefficients

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep


/-- The true native transpose function on the original family degrees. -/
def canonicalFamilyFiniteTransposeFunction := by
  letI := canonicalFamilyFintype k E I hsep
  exact (@ChenRanks.directSumFiniteProductGradingEquiv k inferInstance
    (OriginalMaximalIsotropicFamily (cupQuotient I))
    (canonicalFamilyFintype k E I hsep)
    (SharedCanonicalFamilyDegreeComponent k E I)
    (sharedCanonicalFamilyDegreeMonoids k E I)
    (sharedCanonicalFamilyDegreeCoefficients k E I)).toEquiv



end ChenRanks.Koszul
