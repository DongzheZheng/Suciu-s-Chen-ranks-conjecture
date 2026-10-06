import ChenRanks.ArrangementChenRanksEventual
import ChenRanks.CentralChenRanksEventual
import ChenRanks.ArrangementChenRankSum

/-! The eventual original-group formula in the manuscript's numerical
notation. All component counts remain the native projective counts.
These statements only have an existential stable range. They do not
prove the manuscript's explicit N−1 or N−2 ranges.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (base : A.Complement)

/-- The genuine eventual rational Chen formula, expressed as
(q−1) times the actual resonance-component sum over 2≤m≤N. -/
theorem actualRationalChenRanks_eventual_paperExpression :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q ≥ Q,
      A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal) := by
  obtain ⟨Q, h2, hQ⟩ := A.actualRationalChenRanks_eventual base
  refine ⟨Q, h2, fun q hq => ?_⟩
  exact (hQ q hq).trans
    (congrArg (fun n : ℕ => (n : Cardinal))
      (A.actualResonanceChenRankExpression_eq_range q).symm)

variable (hcentral : ∀ H, A.offset H = 0) (i₀ : ι)

include hcentral i₀ in
/-- The genuine central reduction of the same eventual statement;
the selected hyperplane supplies the actual nonempty decone. -/
theorem actualCentralRationalChenRanks_eventual_paperExpression :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q ≥ Q,
      A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal) := by
  obtain ⟨Q, h2, hQ⟩ := A.actualCentralRationalChenRanks_eventual hcentral i₀ base
  refine ⟨Q, h2, fun q hq => ?_⟩
  exact (hQ q hq).trans
    (congrArg (fun n : ℕ => (n : Cardinal))
      (A.actualResonanceChenRankExpression_eq_range q).symm)

end ChenRanks.AffineArrangement
