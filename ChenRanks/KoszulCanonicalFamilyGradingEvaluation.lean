import ChenRanks.KoszulCanonicalFamilyTransposeObjects

/-! Actual computation of the certified original finite-family
reconstruction using its one shared set of the unchanged original native dictionaries. -/

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

attribute [local instance 3500]
  sharedDegreeParents sharedDegreeCoefficients sharedOriginalParents sharedOriginalCoefficients

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep


/-- The actual reconstruction function is the actual native component
grading function following the actual native transpose. -/
theorem canonicalFamilyHomogeneousDirectSumEquiv_toEquiv_apply
    (x : ⨁ r, CanonicalFamilyHomogeneousDegree k E I r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    (canonicalFamilyHomogeneousDirectSumEquiv k E I hsep).toEquiv x P =
      (sharedCanonicalFamilyComponentEquiv k E I P).toEquiv
        (canonicalFamilyFiniteTransposeFunction k E I hsep x P) := by
  rfl


end ChenRanks.Koszul
