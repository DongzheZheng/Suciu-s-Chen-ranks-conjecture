import ChenRanks.KoszulCanonicalFamilyDefectsFiniteBase

set_option stderrAsMessages false
set_option Elab.async false

/-! The unchanged original scalar parents, native base-restriction
comparisons and literal degree defects. This file asserts no transport,
finite-dimensionality or eventual-bijection premise. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

@[implicit_reducible] private def gradedDefectCycleGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := inferInstance

local instance (priority := 2500) gradedDefectGenericCycleGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := gradedDefectCycleGroup k V

local instance (priority := 2500) gradedDefectGenericOriginalGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance (priority := 2000) gradedDefectSourceGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) gradedDefectSourceMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (gradedDefectSourceGroup k E I).toAddCommMonoid

local instance (priority := 2000) gradedDefectSourceBaseCoefficients :
    _root_.Module k (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleScalarModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

@[implicit_reducible] private def gradedOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) := inferInstance

local instance (priority := 2000) gradedDefectSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  gradedOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

@[implicit_reducible] private def gradedOriginalTower
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : IsScalarTower k (S k V) (Module k V K) := inferInstance

local instance gradedDefectSourceTower :
    IsScalarTower k (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  gradedOriginalTower k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)


local instance (priority := 2000) gradedDefectFamilyGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) gradedDefectFamilyMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) gradedDefectFamilyCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentCoefficients k E I

local instance (priority := 2500) gradedDefectFamilyBaseCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentBaseCoefficients k E I

local instance (priority := 2500) gradedDefectFamilyBaseScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul k (ComponentAmbientModule k E P.val) :=
  fun P => (componentAmbientModuleBaseCoefficients k E P.val).toSMul

local instance (priority := 2500) gradedDefectFamilyScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentScalarActions k E I

local instance gradedDefectFamilyTowers :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      IsScalarTower k (S k (_root_.Module.Dual k E))
        (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleBaseCoefficientScalarTower k E P.val

@[implicit_reducible] private def gradedPiGroup
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    AddCommGroup (∀ i, A i) := inferInstance

@[implicit_reducible] private def gradedPiModule
    (R : Type*) [Semiring R] {ι : Type*} (A : ι → Type*)
    [∀ i, AddCommMonoid (A i)] [∀ i, _root_.Module R (A i)] :
    _root_.Module R (∀ i, A i) := inferInstance

local instance (priority := 2000) gradedDefectTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) :=
  gradedPiGroup (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E P.val)

local instance (priority := 2000) gradedDefectTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  (gradedDefectTargetGroup k E I).toAddCommMonoid

local instance (priority := 2000) gradedDefectTargetCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  gradedPiModule (S k (_root_.Module.Dual k E))
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      ComponentAmbientModule k E P.val)

local instance (priority := 2000) gradedDefectTargetBaseCoefficients :
    _root_.Module k (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetBaseCoefficients k E I

local instance (priority := 2500) gradedDefectTargetBaseScalarAction :
    SMul k (CanonicalFamilyModule k E I) :=
  (gradedDefectTargetBaseCoefficients k E I).toSMul

local instance (priority := 2500) gradedDefectTargetScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  (gradedDefectTargetCoefficients k E I).toSMul

local instance gradedDefectTargetTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetBaseCoefficientScalarTower k E I


local instance (priority := 2000) gradedDefectKernelGroup :
    AddCommGroup (CanonicalFamilyKernel k E I) := canonicalFamilyKernelAddCommGroup k E I

local instance (priority := 2000) gradedDefectKernelMonoid :
    AddCommMonoid (CanonicalFamilyKernel k E I) :=
  (canonicalFamilyKernelAddCommGroup k E I).toAddCommMonoid

local instance (priority := 2000) gradedDefectKernelBaseCoefficients :
    _root_.Module k (CanonicalFamilyKernel k E I) := canonicalFamilyKernelBaseCoefficients k E I

local instance (priority := 2000) gradedDefectCokernelGroup :
    AddCommGroup (CanonicalFamilyCokernel k E I) := canonicalFamilyCokernelAddCommGroup k E I

local instance (priority := 2000) gradedDefectCokernelMonoid :
    AddCommMonoid (CanonicalFamilyCokernel k E I) :=
  (canonicalFamilyCokernelAddCommGroup k E I).toAddCommMonoid

local instance (priority := 2000) gradedDefectCokernelBaseCoefficients :
    _root_.Module k (CanonicalFamilyCokernel k E I) := canonicalFamilyCokernelBaseCoefficients k E I


@[implicit_reducible] private def gradedCycleDegreeGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} (c : _root_.Module.Basis τ k V) (r : ℕ) :
    AddCommGroup (cycleDegree k V c r) := inferInstance

local instance (priority := 2000) gradedGenericCycleDegreeGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} (c : _root_.Module.Basis τ k V) (r : ℕ) :
    AddCommGroup (cycleDegree k V c r) := gradedCycleDegreeGroup k V c r

@[implicit_reducible] private def gradedHomogeneousGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) := inferInstance

local instance (priority := 2000) gradedGenericHomogeneousGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) := gradedHomogeneousGroup k V c K r

local instance (priority := 2000) gradedGenericHomogeneousMonoids
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommMonoid (homogeneousModule k V c K r) :=
  (gradedHomogeneousGroup k V c K r).toAddCommMonoid

@[implicit_reducible] private def gradedHomogeneousModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) := inferInstance

local instance (priority := 2000) gradedGenericHomogeneousModules
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) := gradedHomogeneousModule k V c K r

local instance (priority := 2000) gradedDefectDegreeGroups (r : ℕ) :
    AddCommGroup (CanonicalFamilyHomogeneousDegree k E I r) :=
  gradedPiGroup (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    homogeneousModule k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r)

local instance (priority := 2000) gradedDefectDegreeMonoids (r : ℕ) :
    AddCommMonoid (CanonicalFamilyHomogeneousDegree k E I r) :=
  (gradedDefectDegreeGroups k E I r).toAddCommMonoid

local instance (priority := 2000) gradedDefectDegreeModules (r : ℕ) :
    _root_.Module k (CanonicalFamilyHomogeneousDegree k E I r) :=
  gradedPiModule k (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    homogeneousModule k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r)


/-- The native kernel of base restriction retains exactly the original
kernel and its unchanged base action. -/
def canonicalFamilyKernelBaseEquiv :
    CanonicalFamilyKernel k E I ≃ₗ[k] LinearMap.ker (originalCanonicalFamilyBaseMap k E I) :=
  LinearEquiv.refl k _


@[implicit_reducible] private def gradedQuotientGroup
    (R N : Type*) [Ring R] [AddCommGroup N] [_root_.Module R N]
    (Q : Submodule R N) : AddCommGroup (N ⧸ Q) := inferInstance

local instance (priority := 2500) gradedDefectBaseRangeQuotientGroup :
    AddCommGroup ((CanonicalFamilyModule k E I) ⧸
      LinearMap.range (originalCanonicalFamilyBaseMap k E I)) :=
  gradedQuotientGroup k (CanonicalFamilyModule k E I)
    (LinearMap.range (originalCanonicalFamilyBaseMap k E I))

local instance (priority := 2500) gradedDefectBaseRangeQuotientMonoid :
    AddCommMonoid ((CanonicalFamilyModule k E I) ⧸
      LinearMap.range (originalCanonicalFamilyBaseMap k E I)) :=
  (gradedDefectBaseRangeQuotientGroup k E I).toAddCommMonoid

local instance (priority := 2500) gradedDefectRestrictedRangeQuotientGroup :
    AddCommGroup ((CanonicalFamilyModule k E I) ⧸
      (LinearMap.range (originalCanonicalFamilyModuleMap k E I)).restrictScalars k) :=
  gradedQuotientGroup k (CanonicalFamilyModule k E I)
    ((LinearMap.range (originalCanonicalFamilyModuleMap k E I)).restrictScalars k)

local instance (priority := 2500) gradedDefectRestrictedRangeQuotientMonoid :
    AddCommMonoid ((CanonicalFamilyModule k E I) ⧸
      (LinearMap.range (originalCanonicalFamilyModuleMap k E I)).restrictScalars k) :=
  (gradedDefectRestrictedRangeQuotientGroup k E I).toAddCommMonoid


/-- The native quotient scalar-restriction equivalence retains the
actual original cokernel, not a substitute quotient. -/
def canonicalFamilyCokernelBaseEquiv :
    CanonicalFamilyCokernel k E I ≃ₗ[k]
      ((CanonicalFamilyModule k E I) ⧸ LinearMap.range (originalCanonicalFamilyBaseMap k E I)) :=
  (Submodule.Quotient.restrictScalarsEquiv k
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I))).symm



end ChenRanks.Koszul
