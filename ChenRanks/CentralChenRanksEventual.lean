import ChenRanks.ArrangementChenRanksEventual
import ChenRanks.CentralDeconeComplement
import ChenRanks.CentralDeconeResonanceSummation

/-! The genuine central reduction of the eventual original-group
Chen-rank formula. This candidate retains the actual fundamental group,
cardinal rank and actual native resonance counts. Its range is only
existential: it does not verify the manuscript's effective N−2 range. -/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralChenRanksEventualDecidableEq : DecidableEq ι := Classical.decEq ι
variable (hcentral : ∀ H, A.offset H = 0) (i₀ : ι) (base : A.Complement)

include hcentral i₀ in
theorem actualCentralRationalChenRanks_eventual :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q ≥ Q,
      A.chenRank base (q - 1) =
        (∑ m ∈ Finset.range (Fintype.card ι + 1),
          A.singularProjectiveComponentDimensionCount m *
            ((q - 1) * (m + q - 2).choose q) : ℕ) := by
  let D := A.actualCentralDecone hcentral i₀
  let deconeBase := A.actualCentralSliceToDecone hcentral i₀
    (A.centralSlicePoint hcentral i₀ base)
  obtain ⟨Q, h2, hQ⟩ := D.actualRationalChenRanks_eventual deconeBase
  refine ⟨Q, h2, fun q hq => ?_⟩
  have hi : q - 1 = (q - 2) + 1 := by omega
  have hc : A.chenRank base (q - 1) = D.chenRank deconeBase (q - 1) := by
    simpa only [hi] using A.actualCentralDeconeChenRank_succ hcentral i₀ base (q - 2)
  rw [hc, hQ q hq]
  exact congrArg (fun n : ℕ => (n : Cardinal))
    (A.actualCentralDecone_resonanceWeightedSum hcentral i₀
      (fun m => (q - 1) * (m + q - 2).choose q))

end ChenRanks.AffineArrangement
