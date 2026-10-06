import ChenRanks.KoszulCanonicalFamilyGradingTargetEquiv
import ChenRanks.KoszulFreeDualFamilyDimension

/-!
# The dimension of the genuine finite-family homogeneous target

This computes only the actual finite product of the original
zero-relation Koszul pieces, using their already proved dimensions.
It does not rely on the unverified reconstruction computation rule,
canonical-map bijectivity, an effective bound, or a Chen comparison.
The family is the literal original maximal-isotropic subtype.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

attribute [local instance 2000]
  hilbertHomogeneousGroup hilbertHomogeneousMonoid hilbertHomogeneousBaseCoefficients

local instance (priority := 2000) hilbertFamilyDegreeGroup (r : ℕ) :
    AddCommGroup (CanonicalFamilyHomogeneousDegree k E I r) :=
  canonicalFamilyHomogeneousDegreeAddCommGroup k E I r

local instance (priority := 2000) hilbertFamilyDegreeMonoid (r : ℕ) :
    AddCommMonoid (CanonicalFamilyHomogeneousDegree k E I r) :=
  canonicalFamilyHomogeneousDegreeAddCommMonoid k E I r

local instance (priority := 2000) hilbertFamilyDegreeBaseCoefficients (r : ℕ) :
    _root_.Module k (CanonicalFamilyHomogeneousDegree k E I r) :=
  canonicalFamilyHomogeneousDegreeBaseCoefficients k E I r

variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

include hsep

local instance hilbertFamilyFintype :
    Fintype (OriginalMaximalIsotropicFamily (cupQuotient I)) :=
  canonicalFamilyFintype k E I hsep

/-- Actual target dimension, computed from the true finite family and
the proved free Koszul-piece formula. -/
theorem canonicalFamilyHomogeneousDegree_finrank (r : ℕ) :
    letI := hilbertFamilyFintype k E I hsep
    _root_.Module.finrank k (CanonicalFamilyHomogeneousDegree k E I r) =
      ∑ P : OriginalMaximalIsotropicFamily (cupQuotient I),
        (r + 1) * (_root_.Module.finrank k P.val + r).choose (r + 2) := by
  letI := hilbertFamilyFintype k E I hsep
  exact finiteDualFreeHomogeneousFamily_finrank k E
    (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) => P.val)
    (fun P => canonicalFamilyComponentBasis k E I P) r


end ChenRanks.Koszul
