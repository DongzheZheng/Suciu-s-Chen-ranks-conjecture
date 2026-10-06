import ChenRanks.KoszulCanonicalFamilySharedOriginalParents

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


/-- The already proved original native grading, on the one shared family. -/
def sharedCanonicalFamilyComponentEquiv
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    (⨁ r, SharedCanonicalFamilyDegreeComponent k E I P r) ≃ₗ[k]
      SharedCanonicalFamilyOriginalComponent k E I P :=
  nativeHomogeneousDirectSumEquiv k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥


end ChenRanks.Koszul
