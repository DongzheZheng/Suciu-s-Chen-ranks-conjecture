import ChenRanks.KoszulCanonicalFamilyGradingKernelBaseTransport
import ChenRanks.DirectSumMonoidKernel

set_option stderrAsMessages false
set_option Elab.async false

/-! Actual kernel transport through the already proved original grading
square and the native direct-sum kernel comparison. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

attribute [local instance 2500]
  gradedDefectGenericCycleGroups gradedDefectGenericOriginalGroups
  gradedDefectFamilyBaseCoefficients gradedDefectFamilyBaseScalarActions
  gradedDefectFamilyScalarActions gradedDefectFamilyTowers
  gradedDefectTargetBaseScalarAction gradedDefectTargetScalarAction
  gradedDefectBaseRangeQuotientGroup gradedDefectBaseRangeQuotientMonoid
  gradedDefectRestrictedRangeQuotientGroup gradedDefectRestrictedRangeQuotientMonoid

attribute [local instance 2000]
  gradedDefectSourceGroup gradedDefectSourceMonoid gradedDefectSourceBaseCoefficients
  gradedDefectSourceCoefficients gradedDefectSourceTower
  gradedDefectFamilyGroups gradedDefectFamilyMonoids gradedDefectFamilyCoefficients
  gradedDefectTargetGroup gradedDefectTargetMonoid gradedDefectTargetCoefficients
  gradedDefectTargetBaseCoefficients gradedDefectTargetTower
  gradedDefectKernelGroup gradedDefectKernelMonoid gradedDefectKernelBaseCoefficients
  gradedDefectCokernelGroup gradedDefectCokernelMonoid gradedDefectCokernelBaseCoefficients
  gradedGenericCycleDegreeGroups gradedGenericHomogeneousGroups
  gradedGenericHomogeneousMonoids gradedGenericHomogeneousModules
  gradedDefectDegreeGroups gradedDefectDegreeMonoids gradedDefectDegreeModules

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

/-- The actual direct sum of the unchanged homogeneous-map kernels,
followed only by the native complete grading diagram. The intermediate
return type is obtained from the actual original degree maps. -/
def canonicalFamilyGradingDegreeKernelTransport :=
  ChenRanks.directSumComponentMonoidKernelEquiv k
    (originalCanonicalFamilyHomogeneousMap k E I b)


/-- Actual degree kernels reconstruct the same original ungraded kernel.
Both equivalences act on the native kernels of the original maps; the
codomain is the literal original canonical-family kernel. -/
def canonicalFamilyDegreeKernelDirectSumEquiv :=
  (canonicalFamilyGradingDegreeKernelTransport k E I b).trans
    (canonicalFamilyGradingKernelOriginalTransport k E I b hsep)


end ChenRanks.Koszul
