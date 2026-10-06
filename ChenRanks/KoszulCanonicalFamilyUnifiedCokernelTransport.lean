import ChenRanks.KoszulCanonicalFamilyGradingCokernelOriginalTransport
import ChenRanks.DirectSumStoredDiagramCokernel

/-! A single native cokernel factory for the actual canonical family.
The component and whole target groups below are the original named
native constructors. The proved full diagram supplies every original
map, and the proved original quotient scalar restriction closes the
comparison. No independently built middle quotient is identified by
an implicit comparison of its group or quotient-relation records. -/

set_option stderrAsMessages false
set_option Elab.async false

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

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep


/-- The unchanged actual degree-map cokernels reconstruct the unchanged
original canonical-family cokernel through its true full diagram. -/
def canonicalFamilyUnifiedDegreeCokernelDirectSumEquiv :=
  ChenRanks.directSumStoredDiagramCokernelEquivTo k
    (aM := fun r => registeredHomogeneousMonoids k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r)
    (aN := fun r => registeredFamilyDegreeGroups k E I r)
    (sM := fun r => registeredHomogeneousCoefficients k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r)
    (sN := fun r => registeredFamilyDegreeCoefficients k E I r)
    (aW := gradedDefectSourceMonoid k E I)
    (aZ := gradedDefectTargetGroup k E I)
    (sW := gradedDefectSourceBaseCoefficients k E I)
    (sZ := gradedDefectTargetBaseCoefficients k E I)
    (originalCanonicalFamilyHomogeneousDirectSum_diagram k E I b hsep)
    (canonicalFamilyCokernelBaseEquiv k E I).symm


end ChenRanks.Koszul
