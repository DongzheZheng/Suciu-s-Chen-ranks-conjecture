import ChenRanks.KoszulCanonicalFamilyGradingFunctionEquations

/-! Reuse the native additive parents of the same actual quotient family.
This file caches only existing original Pi/group parent projections. -/
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

/-- Native componentwise additive parent, computed generically before
specializing the actual component quotient aliases. -/
@[implicit_reducible] def functionPiAddMonoid
    {κ : Type*} (A : κ → Type*) [∀ p, AddCommMonoid (A p)] :
    AddMonoid (∀ p, A p) := inferInstance

local instance (priority := 4500) gradingFunctionSharedTargetAddMonoid :
    AddMonoid ((P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      SharedCanonicalFamilyOriginalComponent k E I P) :=
  @functionPiAddMonoid (OriginalMaximalIsotropicFamily (cupQuotient I))
    (SharedCanonicalFamilyOriginalComponent k E I) (sharedCanonicalFamilyOriginalMonoids k E I)

local instance (priority := 4500) gradingFunctionOriginalTargetAddMonoid :
    AddMonoid (CanonicalFamilyModule k E I) :=
  (canonicalFamilyTargetAddCommMonoid k E I).toAddMonoid



end ChenRanks.Koszul
