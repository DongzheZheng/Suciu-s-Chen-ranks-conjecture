import ChenRanks.KoszulCanonicalFamilyFiniteness
import ChenRanks.KoszulCanonicalFamilyEvaluation
import ChenRanks.LocalizedMapKernelCokernel

/-!
# Literal tensor vanishing of the original canonical family's defects

The defects are the actual kernel and the actual quotient by the actual
range of the already constructed original family map. Native localized
kernel comparison and genuine tensor right exactness specialize the
proved actual nonzero-point family bijectivity. Finite generation and
local vanishing are both derived for these exact defects; no vanishing,
support, or defect-comparison premise is supplied.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

@[implicit_reducible] private def defectCycleGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := inferInstance

local instance (priority := 2000) defectOriginalCycleGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := defectCycleGroup k V

local instance (priority := 2000) defectOriginalModuleGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance (priority := 2000) defectSourceGroup :
    AddCommGroup (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  originalModuleAddCommGroup k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) defectSourceMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (defectSourceGroup k E I).toAddCommMonoid

@[implicit_reducible] private def defectOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance (priority := 2000) defectSourceCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  defectOriginalCoefficients k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)

local instance (priority := 2000) defectSourceScalarAction :
    SMul (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (defectSourceCoefficients k E I).toSMul

local instance (priority := 2000) defectFamilyGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) defectFamilyMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) defectFamilyCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentCoefficients k E I

local instance (priority := 2000) defectFamilyScalarActions :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentScalarActions k E I

@[implicit_reducible] private def defectPiGroup
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    AddCommGroup (∀ i, A i) := inferInstance

@[implicit_reducible] private def defectPiModule
    (R : Type*) [Semiring R] {ι : Type*} (A : ι → Type*)
    [∀ i, AddCommMonoid (A i)] [∀ i, _root_.Module R (A i)] :
    _root_.Module R (∀ i, A i) := inferInstance

local instance (priority := 2000) defectTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) :=
  defectPiGroup (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
    ComponentAmbientModule k E P.val)

local instance (priority := 2000) defectTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) :=
  (defectTargetGroup k E I).toAddCommMonoid

local instance (priority := 2000) defectTargetCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  defectPiModule (S k (_root_.Module.Dual k E))
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) =>
      ComponentAmbientModule k E P.val)

local instance (priority := 2000) defectTargetScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I) :=
  (defectTargetCoefficients k E I).toSMul

/-- The native kernel of the very same original canonical family map. -/
abbrev CanonicalFamilyKernel := LinearMap.ker (originalCanonicalFamilyModuleMap k E I)

/-- The native cokernel of the very same original canonical family map. -/
abbrev CanonicalFamilyCokernel :=
  (CanonicalFamilyModule k E I) ⧸ LinearMap.range (originalCanonicalFamilyModuleMap k E I)

@[implicit_reducible] private def defectQuotientGroup
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    (Q : Submodule R M) : AddCommGroup (M ⧸ Q) := inferInstance

@[implicit_reducible] private def defectQuotientModule
    (R M : Type*) [Ring R] [AddCommGroup M] [_root_.Module R M]
    (Q : Submodule R M) : _root_.Module R (M ⧸ Q) := inferInstance

/-- Cached native additive parent of the actual original cokernel. -/
@[implicit_reducible] def canonicalFamilyNativeCokernelAddCommGroup :
    AddCommGroup (CanonicalFamilyCokernel k E I) :=
  defectQuotientGroup (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I)
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

local instance (priority := 2000) defectCokernelGroup :
    AddCommGroup (CanonicalFamilyCokernel k E I) :=
  canonicalFamilyNativeCokernelAddCommGroup k E I

/-- Its actual native additive-monoid parent. -/
@[implicit_reducible] def canonicalFamilyNativeCokernelAddCommMonoid :
    AddCommMonoid (CanonicalFamilyCokernel k E I) :=
  (canonicalFamilyNativeCokernelAddCommGroup k E I).toAddCommMonoid

local instance (priority := 2000) defectCokernelMonoid :
    AddCommMonoid (CanonicalFamilyCokernel k E I) :=
  canonicalFamilyNativeCokernelAddCommMonoid k E I

/-- Cached native quotient action on the actual original cokernel. -/
@[implicit_reducible] def canonicalFamilyNativeCokernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  defectQuotientModule (S k (_root_.Module.Dual k E)) (CanonicalFamilyModule k E I)
    (LinearMap.range (originalCanonicalFamilyModuleMap k E I))

local instance (priority := 2000) defectCokernelCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  canonicalFamilyNativeCokernelCoefficients k E I

local instance (priority := 2000) defectCokernelScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  (canonicalFamilyNativeCokernelCoefficients k E I).toSMul

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep

omit hsep in
/-- Genuine finite generation of the actual original kernel. -/
theorem canonicalFamilyKernel_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E)) (CanonicalFamilyKernel k E I) :=
  originalCanonicalFamilyKernel_finite k E I

/-- Genuine finite generation of the actual original cokernel. -/
theorem canonicalFamilyCokernel_finite :
    _root_.Module.Finite (S k (_root_.Module.Dual k E)) (CanonicalFamilyCokernel k E I) :=
  originalCanonicalFamilyCokernel_finite k E I hsep

/-- Actual local injectivity kills the literal tensor of the actual kernel. -/
theorem canonicalFamilyKernel_evaluation_subsingleton
    (e : E) (he : e ≠ 0) :
    Subsingleton
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
        ⊗[S k (_root_.Module.Dual k E)] CanonicalFamilyKernel k E I) := by
  exact ChenRanks.localizedMapKernel_subsingleton_of_injective
    (S k (_root_.Module.Dual k E))
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
    (pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e)).primeCompl
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I))
    (CanonicalFamilyModule k E I) (originalCanonicalFamilyModuleMap k E I)
    (originalCanonicalFamilyLocalization_bijective_of_nonzero k E I hsep e he).injective

/-- Actual local surjectivity kills the literal tensor of the actual cokernel. -/
theorem canonicalFamilyCokernel_evaluation_subsingleton
    (e : E) (he : e ≠ 0) :
    Subsingleton
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
        ⊗[S k (_root_.Module.Dual k E)] CanonicalFamilyCokernel k E I) := by
  exact ChenRanks.baseChangeCokernel_subsingleton_of_surjective
    (S k (_root_.Module.Dual k E))
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I))
    (CanonicalFamilyModule k E I) (originalCanonicalFamilyModuleMap k E I)
    (originalCanonicalFamilyLocalization_bijective_of_nonzero k E I hsep e he).surjective

end ChenRanks.Koszul
