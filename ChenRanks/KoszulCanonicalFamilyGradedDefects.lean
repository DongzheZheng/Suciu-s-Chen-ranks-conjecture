import ChenRanks.KoszulCanonicalFamilyDegreeKernelFinite
import ChenRanks.KoszulCanonicalFamilyDegreeCokernelFinite
import ChenRanks.FiniteDirectSumStoredDefectsEventual

set_option stderrAsMessages false
set_option Elab.async false

/-! Genuine degree-defect finiteness and existential eventual bijectivity
of the unchanged original canonical maps. The true direct sums are
identified with the original finite-over-base kernel/cokernel in the
preceding transport files. No finite defect, effective bound or Chen
comparison is assumed. -/

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

attribute [local instance 3000]
  gradedDegreeCokernelGroups gradedDegreeCokernelMonoids gradedDegreeCokernelCoefficients

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

variable [IsAlgClosed k]


set_option maxHeartbeats 400000 in
/-- Existential eventual bijectivity of the actual original homogeneous
canonical family map. This gives no explicit AFRS range or Chen comparison. -/
theorem originalCanonicalFamilyHomogeneousMap_eventually_bijective :
    ∃ B : ℕ, ∀ r ≥ B,
      Function.Bijective (originalCanonicalFamilyHomogeneousMap k E I b r) := by
  exact ChenRanks.finiteDirectSumStoredDefects_exists_eventually_bijective k
    (aM := fun r => registeredHomogeneousMonoids k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r)
    (aN := fun r => registeredFamilyDegreeGroups k E I r)
    (sM := fun r => registeredHomogeneousCoefficients k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r)
    (sN := fun r => registeredFamilyDegreeCoefficients k E I r)
    (originalCanonicalFamilyHomogeneousMap k E I b)
    (canonicalFamilyDegreeKernelDirectSum_finite k E I b hsep)
    (canonicalFamilyDegreeCokernelDirectSum_finite k E I b hsep)


end ChenRanks.Koszul
