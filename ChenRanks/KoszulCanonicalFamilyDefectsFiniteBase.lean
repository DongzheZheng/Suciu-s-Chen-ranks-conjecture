import ChenRanks.KoszulCanonicalFamilyDefectLocalization
import ChenRanks.KoszulCanonicalFamilyGrading
import ChenRanks.MixedUniverseOriginSupportedModuleFinite

/-!
# Genuine base-field finiteness of the original canonical-family defects

Both defects remain the native kernel and quotient-by-range of the same
original ambient-linear family map. Their base-field actions are the
original source/target actions, whose compatibility was proved for the
actual symmetric projection. True finite ambient generation and actual
nonzero-point tensor vanishing imply finite base-field dimension by the
proved pure-algebra origin-support argument. No support, finite-base,
grading, or effective-bound conclusion is input.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

@[implicit_reducible] private def baseDefectCycleGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := inferInstance

local instance (priority := 2500) baseDefectGenericCycleGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := baseDefectCycleGroup k V

local instance (priority := 2500) baseDefectGenericOriginalGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def baseDefectOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

@[implicit_reducible] private def baseDefectOriginalTower
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : IsScalarTower k (S k V) (Module k V K) :=
  inferInstance

local instance (priority := 2000) baseDefectSourceGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) baseDefectSourceMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (baseDefectSourceGroup k E I).toAddCommMonoid

local instance (priority := 2000) baseDefectSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  baseDefectOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) baseDefectSourceBaseCoefficients :
    _root_.Module k (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleScalarModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance baseDefectSourceTower :
    IsScalarTower k (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  baseDefectOriginalTower k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) baseDefectFamilyGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) baseDefectFamilyMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) baseDefectFamilyCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentCoefficients k E I

local instance (priority := 2500) baseDefectFamilyBaseCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentBaseCoefficients k E I

local instance (priority := 2500) baseDefectFamilyBaseScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul k (ComponentAmbientModule k E P.val) :=
  fun P => (componentAmbientModuleBaseCoefficients k E P.val).toSMul

local instance (priority := 2500) baseDefectFamilyScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentScalarActions k E I

local instance baseDefectFamilyTowers :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      IsScalarTower k (S k (_root_.Module.Dual k E))
        (ComponentAmbientModule k E P.val) :=
  fun P => componentAmbientModuleBaseCoefficientScalarTower k E P.val

@[implicit_reducible] private def baseDefectPiGroup
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    AddCommGroup (∀ i, A i) := inferInstance

@[implicit_reducible] private def baseDefectPiModule
    (R : Type*) [Semiring R] {ι : Type*} (A : ι → Type*)
    [∀ i, AddCommMonoid (A i)] [∀ i, _root_.Module R (A i)] :
    _root_.Module R (∀ i, A i) := inferInstance

local instance (priority := 2000) baseDefectTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) :=
  baseDefectPiGroup (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E P.val)

local instance (priority := 2000) baseDefectTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  (baseDefectTargetGroup k E I).toAddCommMonoid

local instance (priority := 2000) baseDefectTargetCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  baseDefectPiModule (S k (_root_.Module.Dual k E))
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      ComponentAmbientModule k E P.val)

local instance (priority := 2000) baseDefectTargetBaseCoefficients :
    _root_.Module k (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetBaseCoefficients k E I

local instance (priority := 2500) baseDefectTargetBaseScalarAction :
    SMul k (CanonicalFamilyModule k E I) :=
  (baseDefectTargetBaseCoefficients k E I).toSMul

local instance (priority := 2500) baseDefectTargetScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  (baseDefectTargetCoefficients k E I).toSMul

local instance baseDefectTargetTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  canonicalFamilyTargetBaseCoefficientScalarTower k E I

/-- The actual native submodule additive parent of the original kernel. -/
@[implicit_reducible] def canonicalFamilyKernelAddCommGroup :
    AddCommGroup (CanonicalFamilyKernel k E I) := inferInstance

local instance (priority := 2000) baseDefectKernelGroup :
    AddCommGroup (CanonicalFamilyKernel k E I) := canonicalFamilyKernelAddCommGroup k E I

local instance (priority := 2000) baseDefectKernelMonoid :
    AddCommMonoid (CanonicalFamilyKernel k E I) :=
  (canonicalFamilyKernelAddCommGroup k E I).toAddCommMonoid

/-- The actual native ambient action on the original kernel. -/
@[implicit_reducible] def canonicalFamilyKernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyKernel k E I) := inferInstance

local instance (priority := 2000) baseDefectKernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyKernel k E I) :=
  canonicalFamilyKernelCoefficients k E I

@[implicit_reducible] private def baseDefectQuotientGroup
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    (Q : Submodule R M) : AddCommGroup (M ⧸ Q) := inferInstance

@[implicit_reducible] private def baseDefectQuotientBaseModule
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    [SMul k R] [_root_.Module k M] [IsScalarTower k R M]
    (Q : Submodule R M) : _root_.Module k (M ⧸ Q) :=
  Submodule.Quotient.module' Q

@[implicit_reducible] private def baseDefectQuotientBaseTower
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    [SMul k R] [_root_.Module k M] [IsScalarTower k R M]
    (Q : Submodule R M) : IsScalarTower k R (M ⧸ Q) := inferInstance

/-- The actual native quotient additive parent of the original cokernel. -/
@[implicit_reducible] def canonicalFamilyCokernelAddCommGroup :
    AddCommGroup (CanonicalFamilyCokernel k E I) :=
  baseDefectQuotientGroup (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I)
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

local instance (priority := 2000) baseDefectCokernelGroup :
    AddCommGroup (CanonicalFamilyCokernel k E I) := canonicalFamilyCokernelAddCommGroup k E I

local instance (priority := 2000) baseDefectCokernelMonoid :
    AddCommMonoid (CanonicalFamilyCokernel k E I) :=
  (canonicalFamilyCokernelAddCommGroup k E I).toAddCommMonoid

/-- The actual native ambient quotient action on the original cokernel. -/
@[implicit_reducible] def canonicalFamilyCokernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) := inferInstance

local instance (priority := 2000) baseDefectCokernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  canonicalFamilyCokernelCoefficients k E I

/-- The native submodule action induced by the unchanged original source. -/
@[implicit_reducible] def canonicalFamilyKernelBaseCoefficients :
    _root_.Module k (CanonicalFamilyKernel k E I) := inferInstance

local instance (priority := 2000) baseDefectKernelBaseCoefficients :
    _root_.Module k (CanonicalFamilyKernel k E I) :=
  canonicalFamilyKernelBaseCoefficients k E I

/-- The native quotient action induced by the unchanged original target. -/
@[implicit_reducible] def canonicalFamilyCokernelBaseCoefficients :
    _root_.Module k (CanonicalFamilyCokernel k E I) :=
  baseDefectQuotientBaseModule k (S k (_root_.Module.Dual k E))
    (CanonicalFamilyModule k E I) (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

local instance (priority := 2000) baseDefectCokernelBaseCoefficients :
    _root_.Module k (CanonicalFamilyCokernel k E I) :=
  canonicalFamilyCokernelBaseCoefficients k E I

local instance (priority := 2500) baseDefectKernelBaseScalarAction :
    SMul k (CanonicalFamilyKernel k E I) :=
  (canonicalFamilyKernelBaseCoefficients k E I).toSMul

local instance (priority := 2500) baseDefectCokernelBaseScalarAction :
    SMul k (CanonicalFamilyCokernel k E I) :=
  (canonicalFamilyCokernelBaseCoefficients k E I).toSMul

local instance (priority := 2500) baseDefectCokernelScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  (canonicalFamilyCokernelCoefficients k E I).toSMul

/-- Native submodule compatibility of the unchanged kernel actions. -/
theorem canonicalFamilyKernelBaseCoefficientScalarTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyKernel k E I) := by
  infer_instance

local instance baseDefectKernelTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyKernel k E I) :=
  canonicalFamilyKernelBaseCoefficientScalarTower k E I

/-- Native quotient compatibility of the unchanged cokernel actions. -/
theorem canonicalFamilyCokernelBaseCoefficientScalarTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  baseDefectQuotientBaseTower k (S k (_root_.Module.Dual k E))
    (CanonicalFamilyModule k E I) (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

local instance baseDefectCokernelTower :
    IsScalarTower k (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  canonicalFamilyCokernelBaseCoefficientScalarTower k E I

variable [IsAlgClosed k] [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep

/-- True base-field finiteness of the actual original kernel. -/
theorem canonicalFamilyKernel_finite_over_base :
    _root_.Module.Finite k (CanonicalFamilyKernel k E I) := by
  letI := canonicalFamilyKernel_finite k E I
  exact mixedUniverseOriginSupportedModule_finite_over_base k E
    (CanonicalFamilyKernel k E I)
    (fun e he => canonicalFamilyKernel_evaluation_subsingleton k E I hsep e he)

/-- True base-field finiteness of the actual original cokernel. -/
theorem canonicalFamilyCokernel_finite_over_base :
    _root_.Module.Finite k (CanonicalFamilyCokernel k E I) := by
  letI := canonicalFamilyCokernel_finite k E I hsep
  exact mixedUniverseOriginSupportedModule_finite_over_base k E
    (CanonicalFamilyCokernel k E I)
    (fun e he => canonicalFamilyCokernel_evaluation_subsingleton k E I hsep e he)

end ChenRanks.Koszul
