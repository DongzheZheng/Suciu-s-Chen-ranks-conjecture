import ChenRanks.KoszulCanonicalFamilyGradingInsertion

/-!
# The completely defined original canonical family grading diagram

This definition caches only the original equality of linear maps. Its
body retains the original degree maps, source reconstruction, target
reconstruction and original canonical base map, with their native
scalar actions. It asserts no proof of the equality and supplies no
grading or compatibility premise.
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

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

/-- The original complete diagram as a fully defined proposition. The
equality itself remains to be proved from the actual insertion rules. -/
def canonicalFamilyGradingDiagram : Prop :=
  (canonicalFamilyHomogeneousDirectSumEquiv k E I hsep).toLinearMap ∘ₗ
      DirectSum.lmap (originalCanonicalFamilyHomogeneousMap k E I b) =
    originalCanonicalFamilyBaseMap k E I ∘ₗ
      (homogeneousDirectSumEquiv k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)).toLinearMap

end ChenRanks.Koszul
