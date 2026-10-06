import ChenRanks.KoszulCanonicalGradingOfFormula

/-! One bounded layer of the shared genuine original grading data. -/

set_option stderrAsMessages false

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))


/-- The literal original component degree quotient, cached as one family. -/
abbrev SharedCanonicalFamilyDegreeComponent
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) (r : ℕ) :=
  homogeneousModule k (_root_.Module.Dual k P.val)
    (canonicalFamilyComponentBasis k E I P) ⊥ r


/-- The literal original zero-relation component module. -/
abbrev SharedCanonicalFamilyOriginalComponent
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :=
  Module k (_root_.Module.Dual k P.val) ⊥


end ChenRanks.Koszul
