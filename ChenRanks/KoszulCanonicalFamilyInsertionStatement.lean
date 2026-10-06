import ChenRanks.KoszulCanonicalFamilyGradingTargetEquiv
import ChenRanks.KoszulCanonicalFamilyGradingEvaluation

/-! One cached statement of the original finite-family insertion
equation. This definition is literally the original equality between
the original reconstruction and the original degree inclusion. It
introduces no new map, no grading premise and no asserted equation.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

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

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep

/-- The complete original insertion equality, cached as a definition.
Its body is the same original equality, not a mathematical input. -/
def canonicalFamilyInsertionEquation
    (r : ℕ) (z : CanonicalFamilyHomogeneousDegree k E I r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) : Prop :=
  (canonicalFamilyHomogeneousDirectSumEquiv k E I hsep).toEquiv
      (DirectSum.of (CanonicalFamilyHomogeneousDegree k E I) r z) P =
    degreeQuotientInclusion k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r (z P)

end ChenRanks.Koszul
