import ChenRanks.KoszulCanonicalFamilySharedGradingData
import ChenRanks.FiniteFamilyGradingRecomposition

/-! Actual target reconstruction object using the proved native original
gradings. The sole reconstruction declaration is isolated from its
degree formula, so each native instance specialization is checked in a
bounded module. No target decomposition is supplied as a premise. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

local instance (priority := 2000) registeredFamilyComponentGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommGroups k E I

local instance (priority := 2000) registeredFamilyComponentMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentAddCommMonoids k E I

local instance (priority := 2000) registeredFamilyComponentBaseCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (ComponentAmbientModule k E P.val) :=
  canonicalFamilyComponentBaseCoefficients k E I

local instance (priority := 2000) registeredFamilyTargetGroup :
    AddCommGroup (CanonicalFamilyModule k E I) := canonicalFamilyTargetAddCommGroup k E I

local instance (priority := 2000) registeredFamilyTargetMonoid :
    AddCommMonoid (CanonicalFamilyModule k E I) := canonicalFamilyTargetAddCommMonoid k E I

local instance (priority := 2000) registeredFamilyTargetBaseCoefficients :
    _root_.Module k (CanonicalFamilyModule k E I) := canonicalFamilyTargetBaseCoefficients k E I

local instance (priority := 2500) registeredNativeOriginalGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

local instance (priority := 2500) registeredNativeOriginalMonoid
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommMonoid (Module k V K) :=
  (originalModuleAddCommGroup k V K).toAddCommMonoid

local instance (priority := 2500) registeredNativeOriginalBaseCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module k (Module k V K) :=
  originalModuleScalarModule k V K

local instance (priority := 2000) registeredHomogeneousGroups
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V c K r

local instance (priority := 2000) registeredHomogeneousMonoids
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommMonoid (homogeneousModule k V c K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V c K r).toAddCommMonoid

local instance (priority := 2000) registeredHomogeneousCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V c K r

local instance (priority := 2000) registeredFamilyDegreeGroups (r : ℕ) :
    AddCommGroup (CanonicalFamilyHomogeneousDegree k E I r) :=
  canonicalFamilyHomogeneousDegreeAddCommGroup k E I r

local instance (priority := 2000) registeredFamilyDegreeMonoids (r : ℕ) :
    AddCommMonoid (CanonicalFamilyHomogeneousDegree k E I r) :=
  canonicalFamilyHomogeneousDegreeAddCommMonoid k E I r

local instance (priority := 2000) registeredFamilyDegreeCoefficients (r : ℕ) :
    _root_.Module k (CanonicalFamilyHomogeneousDegree k E I r) :=
  canonicalFamilyHomogeneousDegreeBaseCoefficients k E I r

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep

/-- Genuine reconstruction of the same original finite family target. -/
def canonicalFamilyHomogeneousDirectSumEquiv := by
  letI := canonicalFamilyFintype k E I hsep
  exact @ChenRanks.finiteFamilyGradingRecomposition k inferInstance
    (OriginalMaximalIsotropicFamily (cupQuotient I))
    (canonicalFamilyFintype k E I hsep)
    (SharedCanonicalFamilyDegreeComponent k E I)
    (SharedCanonicalFamilyOriginalComponent k E I)
    (sharedCanonicalFamilyDegreeMonoids k E I)
    (sharedCanonicalFamilyDegreeCoefficients k E I)
    (sharedCanonicalFamilyOriginalMonoids k E I)
    (sharedCanonicalFamilyOriginalCoefficients k E I)
    (sharedCanonicalFamilyComponentEquiv k E I)

end ChenRanks.Koszul
