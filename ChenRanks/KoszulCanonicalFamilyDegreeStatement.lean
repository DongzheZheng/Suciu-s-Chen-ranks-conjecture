import ChenRanks.KoszulCanonicalFamilyGradingStatement

/-! The complete literal original equality in one genuine homogeneous
degree, cached as a fully defined proposition. Its body contains the
unchanged original source and component inclusions and the unchanged
original canonical map. There is no proof, diagram or equivalence field. -/

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
/-- The original one-degree diagram as its complete original equality. -/
def canonicalFamilyDegreeDiagramEquation
    (r : ℕ)
    (z : homogeneousModule k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I) r)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) : Prop :=
    degreeQuotientInclusion k (_root_.Module.Dual k P.val)
        (canonicalFamilyComponentBasis k E I P) ⊥ r
        (originalCanonicalFamilyHomogeneousMap k E I b r z P) =
      originalCanonicalFamilyBaseMap k E I
        (degreeQuotientInclusion k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I) r z) P

end ChenRanks.Koszul
