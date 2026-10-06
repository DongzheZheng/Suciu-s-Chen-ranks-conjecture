import ChenRanks.KoszulCanonicalFamilySharedGradingTypes

/-! One bounded layer of the shared genuine original grading data. -/

set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))


@[implicit_reducible] def sharedCanonicalFamilyDegreeGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → (r : ℕ) →
      AddCommGroup (SharedCanonicalFamilyDegreeComponent k E I P r) :=
  fun P r => canonicalHomogeneousQuotientAddCommGroup k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥ r


@[implicit_reducible] def sharedCanonicalFamilyDegreeMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → (r : ℕ) →
      AddCommMonoid (SharedCanonicalFamilyDegreeComponent k E I P r) :=
  fun P r => (sharedCanonicalFamilyDegreeGroups k E I P r).toAddCommMonoid


local instance (priority := 3000) sharedDegreeParents :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → (r : ℕ) →
      AddCommMonoid (SharedCanonicalFamilyDegreeComponent k E I P r) :=
  sharedCanonicalFamilyDegreeMonoids k E I


@[implicit_reducible] def sharedCanonicalFamilyDegreeCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → (r : ℕ) →
      _root_.Module k (SharedCanonicalFamilyDegreeComponent k E I P r) :=
  fun P r => canonicalHomogeneousQuotientBaseCoefficients k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥ r


local instance (priority := 3000) sharedDegreeCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) → (r : ℕ) →
      _root_.Module k (SharedCanonicalFamilyDegreeComponent k E I P r) :=
  sharedCanonicalFamilyDegreeCoefficients k E I


end ChenRanks.Koszul
