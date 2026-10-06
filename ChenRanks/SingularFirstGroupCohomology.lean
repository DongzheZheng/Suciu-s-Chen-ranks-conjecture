import ChenRanks.SingularFirstCohomologyCharacters
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Actual first singular cohomology and actual bar group cohomology

The group is the existing native based FundamentalGroup, not a chosen
presentation. Its group cohomology is mathlib's inhomogeneous cochain
complex with the actual trivial coefficient representation. The library's
proved degree-one character isomorphism is composed with the genuine
singular loop-evaluation map. No group-cohomology comparison is assumed.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] (k : Type) [Field k]

/-- The actual trivial representation of the actual based fundamental group. -/
abbrev basedFundamentalGroupTrivialRep (base : X) : Rep k (FundamentalGroup X base) :=
  Rep.trivial k (FundamentalGroup X base) k

/-- Actual bar-complex group H¹ of the same group used in ChenObjects. -/
abbrev basedFundamentalGroupH1 (base : X) :=
  groupCohomology.H1 (basedFundamentalGroupTrivialRep X k base)

/-- The actual native bar H¹ isomorphism with actual additive characters.
This is the proved pinned mathlib low-degree theorem, not an input field. -/
def basedFundamentalGroupH1CharactersEquiv (base : X) :
    basedFundamentalGroupH1 X k base ≃ₗ[k] (Additive (FundamentalGroup X base) →+ k) :=
  (groupCohomology.H1IsoOfIsTrivial (basedFundamentalGroupTrivialRep X k base)).toLinearEquiv

/-- The original space's actual singular first cohomology maps to the
actual bar first cohomology of its actual based fundamental group. -/
def firstSingularCohomologyToGroupH1 (base : X) :
    cohomology k X 1 →ₗ[k] basedFundamentalGroupH1 X k base :=
  (basedFundamentalGroupH1CharactersEquiv X k base).symm.toLinearMap.comp
    (firstCohomologyToCharacters X k base)

/-- Its actual additive character is exactly the original loop evaluation. -/
theorem firstSingularCohomologyToGroupH1_character (base : X) (a : cohomology k X 1) :
    basedFundamentalGroupH1CharactersEquiv X k base
        (firstSingularCohomologyToGroupH1 X k base a) =
      firstCohomologyToCharacters X k base a := by
  exact (basedFundamentalGroupH1CharactersEquiv X k base).apply_symm_apply _

/-- The actual map is injective on every genuinely path-connected space.
The inverse construction and degree-two cup comparison remain distinct. -/
theorem firstSingularCohomologyToGroupH1_injective [PathConnectedSpace X] (base : X) :
    Function.Injective (firstSingularCohomologyToGroupH1 X k base) :=
  (basedFundamentalGroupH1CharactersEquiv X k base).symm.injective.comp
    (firstCohomologyToCharacters_injective X k base)

end ChenRanks.SingularCohomology
