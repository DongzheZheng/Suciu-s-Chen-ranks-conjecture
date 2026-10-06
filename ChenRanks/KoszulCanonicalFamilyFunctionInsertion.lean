import ChenRanks.KoszulCanonicalFamilyFunctionComponentInsertion

/-! The genuine original whole functions agree on a genuine direct-sum
insertion. The proposition caches precisely that original equality; it
contains no insertion, compatibility or decomposition evidence. -/

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

/-- The same literal underlying functions on the original direct sum. -/
def canonicalFamilyGradingFunctionInsertionEquation (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) : Prop :=
  canonicalFamilyGradingLeftFunction k E I b hsep
      (DirectSum.of
        (homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I)) r z) =
    canonicalFamilyGradingRightFunction k E I b
      (DirectSum.of
        (homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I)) r z)

/-- Genuine reconstruction and the genuine degree diagram prove this
insertion equality for the unchanged canonical family maps. -/
theorem canonicalFamilyGradingFunctions_insertion (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) :
    canonicalFamilyGradingFunctionInsertionEquation k E I b hsep r z := by
  apply funext
  intro P
  exact canonicalFamilyGradingFunctions_componentInsertion k E I b hsep r z P

end ChenRanks.Koszul
