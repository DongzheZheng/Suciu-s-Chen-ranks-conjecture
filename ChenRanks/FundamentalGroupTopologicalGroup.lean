import ChenRanks.FundamentalGroupHomeomorph
import ChenRanks.FundamentalGroupTopologicalMonoid

/-! The genuine fundamental group of a topological group is abelian
at every actual basepoint. Translation transports the proved identity
case, without a path-connectedness or cyclic-group hypothesis. -/

noncomputable section

namespace ChenRanks

variable (T : Type*) [TopologicalSpace T] [Group T] [IsTopologicalGroup T]

/-- Actual translation carries the original basepoint to the identity. -/
def fundamentalGroupTranslateEquiv (u : T) :
    FundamentalGroup T u ≃* FundamentalGroup T (1 : T) :=
  fundamentalGroupHomeomorphEquivOfEq (Homeomorph.mulLeft u⁻¹) u 1 (by simp)

/-- The actual group structure is retained; commutativity is transported
through the proved original translation equivalence. -/
instance fundamentalGroupTopologicalGroup_commGroup (u : T) :
    CommGroup (FundamentalGroup T u) := by
  letI : CommGroup (FundamentalGroup T (1 : T)) := fundamentalGroupIdentity_commGroup T
  let e := fundamentalGroupTranslateEquiv T u
  let g : Group (FundamentalGroup T u) :=
    inferInstanceAs (Group (CategoryTheory.End (FundamentalGroupoid.mk u)))
  exact
    { g with
      mul_comm := by
        intro x y
        apply e.injective
        rw [map_mul, map_mul, mul_comm] }

end ChenRanks
