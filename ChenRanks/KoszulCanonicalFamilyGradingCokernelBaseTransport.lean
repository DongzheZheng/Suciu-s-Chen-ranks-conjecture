import ChenRanks.KoszulCanonicalFamilyGradingDegreeCokernelTransport
import ChenRanks.LinearMapDiagramMonoidSourceCokernel

/-! Actual native cokernel transport through the already proved original
full grading diagram. Only target quotient groups are used; source
monoids are inferred from the original diagram's stored native parents. -/

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

attribute [local instance 3000]
  gradedDegreeCokernelGroups gradedDegreeCokernelMonoids gradedDegreeCokernelCoefficients

@[implicit_reducible] private def cokernelSharedPiGroup
    {τ : Type*} (A : τ → Type*) [∀ p, AddCommGroup (A p)] :
    AddCommGroup (∀ p, A p) := inferInstance

@[implicit_reducible] private def cokernelSharedPiMonoid
    {τ : Type*} (A : τ → Type*) [∀ p, AddCommMonoid (A p)] :
    AddCommMonoid (∀ p, A p) := inferInstance

@[implicit_reducible] private def cokernelSharedPiCoefficients
    {τ : Type*} (A : τ → Type*) [∀ p, AddCommMonoid (A p)]
    [∀ p, _root_.Module k (A p)] : _root_.Module k (∀ p, A p) := inferInstance

/-- The same native groups whose monoid projections were stored by the
certified target reconstruction factory, rather than recomputed through
the ambient coefficient aliases. -/
local instance (priority := 4000) cokernelSharedOriginalComponentGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (SharedCanonicalFamilyOriginalComponent k E I P) :=
  sharedCanonicalFamilyOriginalGroups k E I

local instance (priority := 4000) cokernelSharedDegreeComponentGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → (r : ℕ) →
      AddCommGroup (SharedCanonicalFamilyDegreeComponent k E I P r) :=
  sharedCanonicalFamilyDegreeGroups k E I

local instance (priority := 4000) cokernelSharedTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) :=
  cokernelSharedPiGroup (SharedCanonicalFamilyOriginalComponent k E I)

local instance (priority := 4000) cokernelSharedTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  cokernelSharedPiMonoid (SharedCanonicalFamilyOriginalComponent k E I)

local instance (priority := 4000) cokernelSharedTargetCoefficients :
    _root_.Module k (CanonicalFamilyModule k E I) :=
  cokernelSharedPiCoefficients k (SharedCanonicalFamilyOriginalComponent k E I)

local instance (priority := 4000) cokernelSharedDegreeTargetGroups (r : ℕ) :
    AddCommGroup (CanonicalFamilyHomogeneousDegree k E I r) :=
  cokernelSharedPiGroup
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      SharedCanonicalFamilyDegreeComponent k E I P r)

local instance (priority := 4000) cokernelSharedDegreeTargetMonoids (r : ℕ) :
    AddCommMonoid (CanonicalFamilyHomogeneousDegree k E I r) :=
  cokernelSharedPiMonoid
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      SharedCanonicalFamilyDegreeComponent k E I P r)

local instance (priority := 4000) cokernelSharedDegreeTargetCoefficients (r : ℕ) :
    _root_.Module k (CanonicalFamilyHomogeneousDegree k E I r) :=
  cokernelSharedPiCoefficients k
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      SharedCanonicalFamilyDegreeComponent k E I P r)


variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep


/-- The proved full grading diagram transports the unchanged native
direct-sum cokernel to the original base-restricted map's cokernel. -/
def canonicalFamilyGradingCokernelBaseTransport :=
  ChenRanks.monoidSourceDiagramCokernelEquiv k
    (originalCanonicalFamilyHomogeneousDirectSum_diagram k E I b hsep)


end ChenRanks.Koszul
