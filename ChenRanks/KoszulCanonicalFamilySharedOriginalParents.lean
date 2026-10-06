import ChenRanks.KoszulCanonicalFamilySharedDegreeParents

/-! One bounded layer of the shared genuine original grading data. -/

set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))


@[implicit_reducible] def sharedCanonicalFamilyOriginalGroups :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommGroup (SharedCanonicalFamilyOriginalComponent k E I P) :=
  fun P => originalModuleAddCommGroup k (_root_.Module.Dual k P.val) ⊥


@[implicit_reducible] def sharedCanonicalFamilyOriginalMonoids :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (SharedCanonicalFamilyOriginalComponent k E I P) :=
  fun P => (sharedCanonicalFamilyOriginalGroups k E I P).toAddCommMonoid


local instance (priority := 3000) sharedOriginalParents :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      AddCommMonoid (SharedCanonicalFamilyOriginalComponent k E I P) :=
  sharedCanonicalFamilyOriginalMonoids k E I


@[implicit_reducible] def sharedCanonicalFamilyOriginalCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (SharedCanonicalFamilyOriginalComponent k E I P) :=
  fun P => originalModuleScalarModule k (_root_.Module.Dual k P.val) ⊥


local instance (priority := 3000) sharedOriginalCoefficients :
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) →
      _root_.Module k (SharedCanonicalFamilyOriginalComponent k E I P) :=
  sharedCanonicalFamilyOriginalCoefficients k E I


end ChenRanks.Koszul
