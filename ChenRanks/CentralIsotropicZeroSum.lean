import ChenRanks.CentralRadialResonanceDirection
import ChenRanks.ArrangementEquationQuadraticCup
import ChenRanks.ResonanceMaximalIsotropicCover

/-! Every genuine central isotropic subspace of dimension at least two
is contained in the actual zero-sum coefficient hyperplane. The true
radial cup-cycle determinant is used on two actual independent vectors;
finite dimension provides such a second vector. -/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ H, A.offset H = 0)

include hcentral in
theorem actualCentralIsotropic_totalCoefficients_zero
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsIsotropic (relationWedge A.equationQuadraticCup) P)
    (hdim : 2 ≤ Module.finrank ℂ P) (a : ι → ℂ) (ha : a ∈ P) :
    (∑ H, a H) = 0 := by
  by_cases haz : a = 0
  · simp only [haz, Pi.zero_apply, Finset.sum_const_zero]
  have hex : ∃ b ∈ P, b ∉ ℂ ∙ a := by
    by_contra hn
    have hle : P ≤ ℂ ∙ a := by
      intro b hb
      by_contra hbn
      exact hn ⟨b, hb, hbn⟩
    have hfin := Submodule.finrank_mono hle
    rw [finrank_span_singleton haz] at hfin
    omega
  obtain ⟨b, hb, hba⟩ := hex
  have hab : ∀ t : ℂ, b ≠ t • a := by
    intro t h
    apply hba
    rw [h]
    exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self a)
  have hcup : A.singularCup (A.equationWindingClassMap a)
      (A.equationWindingClassMap b) = 0 := by
    have he := hP a ha b hb
    simpa only [relationWedge_apply, A.equationQuadraticCup_exteriorWedge] using he
  exact (A.actualCentralCup_independent_totalCoefficients_zero
    hcentral a b haz hab hcup).1

end ChenRanks.AffineArrangement
