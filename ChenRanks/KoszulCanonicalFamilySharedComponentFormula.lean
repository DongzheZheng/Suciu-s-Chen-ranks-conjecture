import ChenRanks.KoszulCanonicalFamilySharedComponentEquiv

/-! One bounded layer of the shared genuine original grading data. -/

set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

attribute [local instance 3000]
  sharedDegreeParents sharedDegreeCoefficients sharedOriginalParents sharedOriginalCoefficients


/-- The shared equivalence keeps the true original degree inclusion. -/
theorem sharedCanonicalFamilyComponentEquiv_toEquiv_of
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) (r : ℕ)
    (z : SharedCanonicalFamilyDegreeComponent k E I P r) :
    (sharedCanonicalFamilyComponentEquiv k E I P).toEquiv
      (DirectSum.of (SharedCanonicalFamilyDegreeComponent k E I P) r z) =
      degreeQuotientInclusion k (_root_.Module.Dual k P.val)
        (canonicalFamilyComponentBasis k E I P) ⊥ r z :=
  nativeHomogeneousDirectSumEquiv_toEquiv_of k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥ r z


end ChenRanks.Koszul
