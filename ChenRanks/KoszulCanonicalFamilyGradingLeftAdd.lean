import ChenRanks.KoszulCanonicalFamilyGradingLeftAddHom
import ChenRanks.SharedExactTactic

/-! One complete original function equation, derived from the actual
native additive-map composite. The equality cache contains exactly the
unchanged original function formula, with no proof premise. -/
set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

/- Reuse the very same original target operation parents stored in the
unchanged function objects; no second operation dictionary is built. -/
attribute [local instance 4000] gradingFunctionTargetZero gradingFunctionTargetAdd
attribute [local instance 4500]
  gradingFunctionSharedTargetAddMonoid gradingFunctionOriginalTargetAddMonoid
attribute [local instance 5000] gradingLeftTargetAddZero

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

local instance (priority := 5000) gradingLeftAddFamilyGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (SharedCanonicalFamilyOriginalComponent k E I P) :=
  sharedCanonicalFamilyOriginalGroups k E I

@[implicit_reducible] private def leftAddCycleAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V] :
    AddCommGroup (LinearMap.ker (delta1 k V)) := inferInstance

local instance (priority := 5000) gradingLeftAddFamilyCycleGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (LinearMap.ker (delta1 k (_root_.Module.Dual k P.val))) :=
  fun P => leftAddCycleAddCommGroup k (_root_.Module.Dual k P.val)

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)



/-- The actual native composite proves the full original add formula. -/
theorem canonicalFamilyGradingLeftFunction_add
    (x y : ⨁ r, homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) :
    canonicalFamilyGradingLeftAddEquation k E I b hsep x y := by
  exact_shared_native (canonicalFamilyGradingLeftAddHom k E I b hsep).map_add x y


end ChenRanks.Koszul
