import ChenRanks.KoszulCanonicalFamilyDegreeStatement

/-! The original canonical family map commutes with the actual original
component maps in one genuine homogeneous degree. No diagram premise
or eventual/effective decomposition is assumed. -/

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

include hsep

omit hsep [CharZero k] in
/-- The actual original homogeneous diagram in one degree, on each true component. -/
theorem originalCanonicalFamilyHomogeneousMap_degreeDiagram
    (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I) r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    canonicalFamilyDegreeDiagramEquation k E I b r z P := by
  have h := isotropicComponentHomogeneousMap_originalDiagram k E I P.val b
    (canonicalFamilyComponentBasis k E I P) (canonicalFamily_component_isotropy k E I P) r z
  have ht := homogeneousOriginalDegree_val_eq_inclusion k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) (⊥ : Submodule k (⋀[k]^2 (_root_.Module.Dual k P.val))) r
    (isotropicComponentHomogeneousMap k E I P.val b
      (canonicalFamilyComponentBasis k E I P) (canonicalFamily_component_isotropy k E I P) r z)
  have hs := homogeneousOriginalDegree_val_eq_inclusion k (_root_.Module.Dual k E) b
    (exteriorAnnihilator k E 2 I) r z
  exact ht.symm.trans (h.trans (congrArg
    (isotropicComponentModuleMap k E I P.val (canonicalFamily_component_isotropy k E I P)) hs))

end ChenRanks.Koszul
