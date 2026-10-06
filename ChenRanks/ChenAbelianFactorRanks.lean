import ChenRanks.ChenSeriesTransport

/-!
# Actual rational Chen spaces under an abelian direct factor

The equivalence of genuine lower-central quotients of the actual
metabelian quotient is rationalized by the native tensor base-change
equivalence. This proves the group-theoretic Chen-rank invariance used
in the manuscript's central deconing argument. It does not identify an
arrangement complement with a decone product, or prove the stable formula.
-/

noncomputable section

namespace ChenRanks

universe u v

variable (G : Type u) (A : Type v) [Group G] [CommGroup A]

/-- Genuine rationalization of the proved actual quotient equivalence,
in the manuscript's ordinary Chen degree `n + 2`. -/
def rationalChenProductSuccEquiv (n : ℕ) :
    rationalChenSpace (G × A) (n + 1) ≃ₗ[ℚ] rationalChenSpace G (n + 1) :=
  ((metabelianLowerCentralProductPieceSuccEquiv G A n).toAdditive.toIntLinearEquiv).baseChange
    ℤ ℚ _ _

/-- The natural-valued dimensions agree because the actual rational
spaces are equivalent. No finiteness of either space is asserted here. -/
theorem finiteChenRank_product_succ (n : ℕ) :
    finiteChenRank (G × A) (n + 1) = finiteChenRank G (n + 1) :=
  (rationalChenProductSuccEquiv G A n).finrank_eq

/-- The cardinal-valued rational Chen ranks also agree, after the
universe lifts required for groups in different universes. This retains
possible infinite dimensions rather than converting them to zero. -/
theorem rationalChenRank_product_succ (n : ℕ) :
    Cardinal.lift.{u} (rationalChenRank (G × A) (n + 1)) =
      Cardinal.lift.{max u v} (rationalChenRank G (n + 1)) :=
  (rationalChenProductSuccEquiv G A n).lift_rank_eq

end ChenRanks
