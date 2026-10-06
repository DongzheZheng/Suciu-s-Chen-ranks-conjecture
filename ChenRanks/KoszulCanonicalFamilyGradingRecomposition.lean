import ChenRanks.KoszulCanonicalFamilyGradingTargetEquiv
import ChenRanks.KoszulCanonicalGradingOfFormula
import ChenRanks.FiniteFamilyGradingTransposeOf
import ChenRanks.KoszulCanonicalFamilyGradingEvaluation
import ChenRanks.FunctionInsertionEquation
import ChenRanks.KoszulCanonicalFamilyInsertionStatement

set_option stderrAsMessages false
set_option Elab.async false


/-! Actual finite-product/direct-sum reconstruction of the same original
canonical family target. The native scalar structures are the cached
original structures; the genuine equivalence and its degree-insertion
formula are derived, with no decomposition or diagram premise. -/

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


/-- The genuine target reconstruction evaluates the same original
underlying insertion at the same original degree inclusion. -/
theorem canonicalFamilyHomogeneousDirectSumEquiv_toEquiv_of
    (r : ℕ) (z : CanonicalFamilyHomogeneousDegree k E I r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    canonicalFamilyInsertionEquation k E I hsep r z P := by
  classical
  letI := canonicalFamilyFintype k E I hsep
  exact ChenRanks.function_insertion_equation
    (fun x : ⨁ n, CanonicalFamilyHomogeneousDegree k E I n =>
      (canonicalFamilyHomogeneousDirectSumEquiv k E I hsep).toEquiv x P)
    (fun x : ⨁ n, CanonicalFamilyHomogeneousDegree k E I n =>
      canonicalFamilyFiniteTransposeFunction k E I hsep x P)
    (sharedCanonicalFamilyComponentEquiv k E I P).toEquiv
    (DirectSum.of (CanonicalFamilyHomogeneousDegree k E I) r z)
    (DirectSum.of (SharedCanonicalFamilyDegreeComponent k E I P) r (z P))
    (degreeQuotientInclusion k (_root_.Module.Dual k P.val)
      (canonicalFamilyComponentBasis k E I P) ⊥ r (z P))
    (canonicalFamilyHomogeneousDirectSumEquiv_toEquiv_apply k E I hsep
      (DirectSum.of (CanonicalFamilyHomogeneousDegree k E I) r z) P)
    (@ChenRanks.directSumFiniteProductGradingEquiv_toEquiv_of k inferInstance
      (OriginalMaximalIsotropicFamily (cupQuotient I))
      (canonicalFamilyFintype k E I hsep)
      (SharedCanonicalFamilyDegreeComponent k E I)
      (sharedCanonicalFamilyDegreeMonoids k E I)
      (sharedCanonicalFamilyDegreeCoefficients k E I) r z P)
    (sharedCanonicalFamilyComponentEquiv_toEquiv_of k E I P r (z P))

end ChenRanks.Koszul

