import ChenRanks.KoszulCanonicalFamilyGradedDegreeObjects
import ChenRanks.LinearMapDiagramMonoidKernel

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

include hsep


/-- The original full grading diagram transports the native direct-sum
kernel to the kernel of the same base-restricted canonical map.  Its
return type is inferred from the actual proved diagram, before any
composition with the original scalar-restriction comparison. -/
def canonicalFamilyGradingKernelBaseTransport :=
  ChenRanks.monoidDiagramKernelEquiv k
    (originalCanonicalFamilyHomogeneousDirectSum_diagram k E I b hsep)



/-- The same native transport, followed only by the proved original
kernel/base-restriction identification. -/
def canonicalFamilyGradingKernelOriginalTransport :=
  (canonicalFamilyGradingKernelBaseTransport k E I b hsep).trans
    (canonicalFamilyKernelBaseEquiv k E I).symm


end ChenRanks.Koszul
