import ChenRanks.KoszulCanonicalFamilyGradedDefectObjects

set_option stderrAsMessages false
set_option Elab.async false

/-! The literal original homogeneous-map defects, separate from the
native parent caches. The cokernel spells out the exact same native
`Quotient (Submodule.quotientRel range)` used by mathlib's quotient
notation; no quotient equivalence or new module is supplied as input. -/

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

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

/-- The true kernel of the unchanged actual degree map. -/
abbrev CanonicalFamilyDegreeKernel (r : ℕ) :=
  LinearMap.ker (originalCanonicalFamilyHomogeneousMap k E I b r)


/-- The true cokernel of the unchanged actual degree map. Its native
quotient relation is the one behind the ordinary submodule quotient. -/
abbrev CanonicalFamilyDegreeCokernel (r : ℕ) :=
  _root_.Quotient
    (LinearMap.range (originalCanonicalFamilyHomogeneousMap k E I b r)).quotientRel


end ChenRanks.Koszul
