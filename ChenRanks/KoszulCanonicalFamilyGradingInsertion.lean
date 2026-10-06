import ChenRanks.KoszulCanonicalFamilyGradingRecomposition

set_option stderrAsMessages false
set_option Elab.async false


/-! The genuine linear insertion rule for the same original finite-family
reconstruction. This short module isolates its native linear-map wrapper
from the preceding underlying-function rule. The scalar actions and the
actual component inclusions are unchanged. -/

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
  registeredHomogeneousGroups registeredHomogeneousMonoids registeredHomogeneousCoefficients
  registeredFamilyDegreeGroups registeredFamilyDegreeMonoids registeredFamilyDegreeCoefficients

attribute [local instance 3500]
  sharedDegreeParents sharedDegreeCoefficients sharedOriginalParents sharedOriginalCoefficients

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep


/-- A real original linear degree insertion goes to the same actual
component inclusion. The underlying insertion formula is the preceding
theorem; no additional action or diagram input is used. -/
theorem canonicalFamilyHomogeneousDirectSumEquiv_lof
    (r : ℕ) (z : CanonicalFamilyHomogeneousDegree k E I r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    canonicalFamilyInsertionEquation k E I hsep r z P := by
  exact canonicalFamilyHomogeneousDirectSumEquiv_toEquiv_of k E I hsep r z P


end ChenRanks.Koszul
