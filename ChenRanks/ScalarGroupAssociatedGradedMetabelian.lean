import ChenRanks.ScalarGroupAssociatedGraded
import ChenRanks.GroupAssociatedGradedMetabelian

/-!
# Actual scalar extension preserves the original Chen metabelianity

The real native Lie derived ideals commute with the native Lie base
change bracket. Applying actual Lie-submodule scalar extension to the
proved original rational second-derived-ideal identity yields the scalar
identity. This does not assume that a group/holonomy comparison exists.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable (k : Type*) [Field k] [CharZero k]
variable (G : Type*) [Group G]

/-- Native derived-ideal base change preserves the actual original
second-derived vanishing, using the original group's actual condition. -/
theorem scalarGroupAssociatedGraded_second_derived_eq_bot
    (hD : derivedSeries G 2 = ⊥) :
    LieAlgebra.derivedSeries k (scalarGroupAssociatedGraded k G) 2 = ⊥ := by
  have hQ : ⁅⁅(⊤ : LieIdeal ℚ (rationalGroupAssociatedGraded G)), ⊤⁆,
      ⁅(⊤ : LieIdeal ℚ (rationalGroupAssociatedGraded G)), ⊤⁆⁆ = ⊥ :=
    rationalGroupAssociatedGraded_second_derived_eq_bot G hD
  have h := congrArg (fun I : LieIdeal ℚ (rationalGroupAssociatedGraded G) =>
    I.baseChange k) hQ
  dsimp only at h
  rw [LieSubmodule.lie_baseChange, LieSubmodule.lie_baseChange,
    LieSubmodule.baseChange_top, LieSubmodule.baseChange_bot] at h
  exact h

/-- Final application uses the actual native maximal metabelian
quotient of the original group, with its second derived subgroup proved
zero. No metabelianity input remains. -/
theorem scalarChenAssociatedGraded_second_derived_eq_bot :
    LieAlgebra.derivedSeries k (scalarChenAssociatedGraded k G) 2 = ⊥ :=
  scalarGroupAssociatedGraded_second_derived_eq_bot k (metabelianQuotient G)
    (metabelianQuotient_second_derived G)

/-- Scalarized actual Chen degree n+1 has the same finite rank as the
original rationalization of that very same group quotient. -/
theorem scalarChenPiece_finrank (n : ℕ) :
    _root_.Module.finrank k (scalarLowerCentralPiece k (metabelianQuotient G) n) =
      finiteChenRank G n :=
  scalarLowerCentralPiece_finrank k (metabelianQuotient G) n

end ChenRanks
