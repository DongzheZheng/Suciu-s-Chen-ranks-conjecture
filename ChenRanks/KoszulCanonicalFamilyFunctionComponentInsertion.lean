import ChenRanks.KoszulCanonicalFamilyDegreeDiagram
import ChenRanks.KoszulCanonicalFamilyGradingFunctions

/-! Actual pointwise component evaluation on the same original degree
insertion. This short leaf composes genuine original computation
identities without rewriting a whole finite-product equality. -/

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

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

/-- The unchanged actual component of the unchanged original function equation. -/
def canonicalFamilyGradingFunctionComponentInsertionEquation (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) : Prop :=
  canonicalFamilyGradingLeftFunction k E I b hsep
      (DirectSum.of
        (homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I)) r z) P =
    canonicalFamilyGradingRightFunction k E I b
      (DirectSum.of
        (homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I)) r z) P

/-- Genuine lmap, reconstruction, one-degree and source insertion
formulas compose to the same actual pointwise function equation. -/
theorem canonicalFamilyGradingFunctions_componentInsertion (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    canonicalFamilyGradingFunctionComponentInsertionEquation k E I b hsep r z P := by
  classical
  letI := canonicalFamilyFintype k E I hsep
  have hf := congrArg
    (fun x : ⨁ n, CanonicalFamilyHomogeneousDegree k E I n =>
      (canonicalFamilyHomogeneousDirectSumEquiv k E I hsep).toEquiv x P)
    (DirectSum.lmap_of (originalCanonicalFamilyHomogeneousMap k E I b) r z)
  have he := canonicalFamilyHomogeneousDirectSumEquiv_toEquiv_of k E I hsep r
    (originalCanonicalFamilyHomogeneousMap k E I b r z) P
  have hd := originalCanonicalFamilyHomogeneousMap_degreeDiagram k E I b r z P
  have hs := congrArg (fun x => originalCanonicalFamilyBaseMap k E I x P)
    (assembleHomogeneous_lof k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r z)
  exact hf.trans (he.trans (hd.trans hs.symm))

end ChenRanks.Koszul
