import ChenRanks.ArrangementChenHomogeneousKoszulComparison
import ChenRanks.KoszulCanonicalFamilyHilbertFormula
import ChenRanks.ActualArrangementRationalFamilyComparison
import ChenRanks.ArrangementSingularProjectiveComponents

/-! The original Chen rank and actual native resonance-component counts.
This candidate combines the same original homogeneous Koszul map with
its genuine original-group comparison. The bound in this file is
existential. It is not the manuscript's effective N−1 bound and is not
a certificate of that stronger final theorem. -/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
open Koszul Resonance LieComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (base : A.Complement)

attribute [local instance 3000]
  arrangementChenOriginalDegreeGroup arrangementChenOriginalDegreeMonoid
  arrangementChenOriginalDegreeScalars

local instance originalChenHilbertFamilyFintype :
    Fintype (OriginalMaximalIsotropicFamily (cupQuotient A.rationalQuadraticKernel)) :=
  canonicalFamilyFintype ℂ (ι → ℂ) A.rationalQuadraticKernel
    A.rationalQuadraticKernel_all_maximal_cupQuotient_separated

private theorem originalChenHilbertFamilyDimensionCount (m : ℕ) :
    Fintype.card {P : OriginalMaximalIsotropicFamily (cupQuotient A.rationalQuadraticKernel) //
        _root_.Module.finrank ℂ P.val = m} =
      A.singularProjectiveComponentDimensionCount m := by
  classical
  calc
    _ = A.rationalKernelQuotientDimensionCount m := by
      unfold rationalKernelQuotientDimensionCount originalMaximalIsotropicDimensionCount
      rfl
    _ = A.rationalMaximalIsotropicDimensionCount m :=
      A.rationalKernelQuotientDimensionCount_eq_original m
    _ = _ := (A.singularProjectiveComponentDimensionCount_eq_rational m).symm

set_option maxHeartbeats 400000 in
/-- Eventual finite Chen ranks use the original actual group quotients
and native resonance-component counts, with no mathematical comparison,
separation or formula input. The stable bound here is existential. -/
theorem actualFiniteChenRanks_eventual :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q ≥ Q,
      finiteChenRank (FundamentalGroup A.Complement base) (q - 1) =
        ∑ m ∈ Finset.range (Fintype.card ι + 1),
          A.singularProjectiveComponentDimensionCount m *
            ((q - 1) * (m + q - 2).choose q) := by
  obtain ⟨B, hB⟩ := originalCanonicalFamilyHomogeneous_eventual_counted_finrank
    ℂ (ι → ℂ) A.rationalQuadraticKernel
    A.rationalQuadraticKernel_all_maximal_cupQuotient_separated
    A.actualLogHolonomyLabelBasis.dualBasis
  refine ⟨B + 2, by omega, fun q hq => ?_⟩
  have h2 : 2 ≤ q := by omega
  have hr : B ≤ q - 2 := by omega
  have hi : q - 1 = (q - 2) + 1 := by omega
  rw [hi, A.actualFiniteChenRank_eq_originalKoszulDegree base (q - 2),
    hB (q - 2) hr, _root_.Module.finrank_fintype_fun_eq_card]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [A.originalChenHilbertFamilyDimensionCount m]
  have he : m + (q - 2) = m + q - 2 := by omega
  have hd : q - 2 + 2 = q := by omega
  rw [he, hd]

/-- The original cardinal-valued rank is retained. Finite-dimensionality
of each actual Chen quotient was proved before converting its rank. -/
theorem actualRationalChenRanks_eventual :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q ≥ Q,
      A.chenRank base (q - 1) =
        (∑ m ∈ Finset.range (Fintype.card ι + 1),
          A.singularProjectiveComponentDimensionCount m *
            ((q - 1) * (m + q - 2).choose q) : ℕ) := by
  obtain ⟨Q, h2, hQ⟩ := A.actualFiniteChenRanks_eventual base
  refine ⟨Q, h2, fun q hq => ?_⟩
  change rationalChenRank (FundamentalGroup A.Complement base) (q - 1) = _
  rw [← finiteChenRank_eq_rationalChenRank, hQ q hq]

end ChenRanks.AffineArrangement
