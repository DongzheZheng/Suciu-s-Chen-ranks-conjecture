import ChenRanks.ArrangementChenRanksAFRSVersionOne
import ChenRanks.CentralDeconeComplement
import ChenRanks.CentralDeconeResonanceSummation

/-!
# Chen ranks of central arrangements

Deconing improves the affine stable range by one degree. The complement
comparison and the preservation of resonance-component counts are derived
from the central arrangement. The only external mathematical input is
`AFRSEffectiveCanonicalDecomposition`, as in the affine theorem.
-/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
universe u
variable {d : ℕ} {ι : Type u} [Fintype ι] (A : AffineArrangement d ι)
local instance centralChenAFRSVersionOneDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The decone preserves the literal intrinsic resonance expression,
not merely a chosen list of components or an eventual numerical formula. -/
theorem actualCentralDecone_resonanceChenRankExpression
    (hcentral : ∀ H, A.offset H = 0) (i₀ : ι) (q : ℕ) :
    (A.actualCentralDecone hcentral i₀).actualResonanceChenRankExpression q =
      A.actualResonanceChenRankExpression q := by
  rw [(A.actualCentralDecone hcentral i₀).actualResonanceChenRankExpression_eq_range,
    A.actualResonanceChenRankExpression_eq_range]
  exact A.actualCentralDecone_resonanceWeightedSum hcentral i₀
    (fun m => (q - 1) * (m + q - 2).choose q)

private theorem centralAFRS_deconeRange (i₀ : ι) (q : ℕ)
    (hq : max 2 (Fintype.card ι - 2) ≤ q) :
    max 2 (Fintype.card (A.ActualCentralDeconeLabels i₀) - 1) ≤ q := by
  rw [A.actualCentralDecone_card i₀]
  omega

/-- Version 1.0 uses the same single general AFRS input as the affine
formula. The actual decone and all actual group/count comparisons are
internal. An empty label type is handled by the proved small boundary. -/
theorem actualCentralRationalChenRanks_paperRange_versionOne
    (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (hcentral : ∀ H, A.offset H = 0) (base : A.Complement)
    (q : ℕ) (hq : max 2 (Fintype.card ι - 2) ≤ q) :
    A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal) := by
  classical
  have h2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  by_cases hι : Nonempty ι
  · let i₀ : ι := Classical.choice hι
    let D := A.actualCentralDecone hcentral i₀
    let deconeBase := A.actualCentralSliceToDecone hcentral i₀
      (A.centralSlicePoint hcentral i₀ base)
    have hi : q - 1 = (q - 2) + 1 := by omega
    have hc : A.chenRank base (q - 1) = D.chenRank deconeBase (q - 1) := by
      simpa only [hi] using A.actualCentralDeconeChenRank_succ hcentral i₀ base (q - 2)
    calc
      A.chenRank base (q - 1) = D.chenRank deconeBase (q - 1) := hc
      _ = (D.actualResonanceChenRankExpression q : Cardinal) :=
        D.actualRationalChenRanks_paperRange_versionOne hAFRS deconeBase q
          (A.centralAFRS_deconeRange i₀ q hq)
      _ = (A.actualResonanceChenRankExpression q : Cardinal) :=
        congrArg (fun n : ℕ => (n : Cardinal))
          (A.actualCentralDecone_resonanceChenRankExpression hcentral i₀ q)
  · letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    have hN : Fintype.card ι ≤ 2 := by
      simp only [Fintype.card_eq_zero]
      omega
    exact A.actualRationalChenRanks_allDegrees_of_atMostTwoHyperplanes base hN q h2

/-- The same actual central-group formula in the literal numerical
notation of the paper, retaining native projective component counts. -/
theorem actualCentralRationalChenRanks_paperSum_versionOne
    (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (hcentral : ∀ H, A.offset H = 0) (base : A.Complement)
    (q : ℕ) (hq : max 2 (Fintype.card ι - 2) ≤ q) :
    A.chenRank base (q - 1) =
      ((q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q : ℕ) := by
  simpa only [actualResonanceChenRankExpression] using
    A.actualCentralRationalChenRanks_paperRange_versionOne hAFRS hcentral base q hq

end ChenRanks.AffineArrangement
