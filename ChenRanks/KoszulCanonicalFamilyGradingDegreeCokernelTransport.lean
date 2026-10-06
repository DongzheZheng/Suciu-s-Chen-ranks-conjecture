import ChenRanks.KoszulCanonicalFamilyGradedKernelTransport
import ChenRanks.DirectSumGradedKernelCokernel

set_option stderrAsMessages false
set_option Elab.async false

/-! The literal degree quotients reconstruct the quotient of the actual
direct-sum map. Each quotient action comes from the unchanged native
range submodule and original target action. No cokernel comparison is input. -/

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

@[implicit_reducible] private def degreeCokernelNativeQuotientGroup
    (N : Type*) [AddCommGroup N] [_root_.Module k N]
    (Q : Submodule k N) : AddCommGroup (N ⧸ Q) := inferInstance

@[implicit_reducible] private def degreeCokernelNativeQuotientCoefficients
    (N : Type*) [AddCommGroup N] [_root_.Module k N]
    (Q : Submodule k N) : _root_.Module k (N ⧸ Q) := inferInstance

local instance (priority := 3000) gradedDegreeCokernelGroups (r : ℕ) :
    AddCommGroup (CanonicalFamilyDegreeCokernel k E I b r) :=
  degreeCokernelNativeQuotientGroup k (CanonicalFamilyHomogeneousDegree k E I r)
    (LinearMap.range (originalCanonicalFamilyHomogeneousMap k E I b r))

local instance (priority := 3000) gradedDegreeCokernelMonoids (r : ℕ) :
    AddCommMonoid (CanonicalFamilyDegreeCokernel k E I b r) :=
  (gradedDegreeCokernelGroups k E I b r).toAddCommMonoid

local instance (priority := 3000) gradedDegreeCokernelCoefficients (r : ℕ) :
    _root_.Module k (CanonicalFamilyDegreeCokernel k E I b r) :=
  degreeCokernelNativeQuotientCoefficients k (CanonicalFamilyHomogeneousDegree k E I r)
    (LinearMap.range (originalCanonicalFamilyHomogeneousMap k E I b r))



/-- Native degree quotients reconstruct the cokernel of the original
direct-sum map. Its type is inferred from the unchanged actual maps. -/
def canonicalFamilyGradingDegreeCokernelTransport :=
  (ChenRanks.directSumComponentCokernelEquiv k
    (homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I))
    (CanonicalFamilyHomogeneousDegree k E I)
    (originalCanonicalFamilyHomogeneousMap k E I b)).symm



end ChenRanks.Koszul
