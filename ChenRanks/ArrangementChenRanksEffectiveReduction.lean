import ChenRanks.ArrangementChenRanksPaperStatements
import ChenRanks.KoszulCanonicalFamilyDegreeHilbertReduction
import ChenRanks.KoszulCanonicalFamilySmallAmbient

/-!
# The precise remaining effective input and the actual Chen endpoint

The first theorem is explicitly conditional on the original canonical
Koszul map being bijective in the paper's effective degree range.
Neither that assertion nor its geometric proof is supplied by this
file.  The actual arrangement separation, group comparison, finite
rational ranks and native resonance counts are already proved inputs
from the current dependency chain.  The second theorem discharges the
degree-map hypothesis internally in the dimension-zero, one and two
boundary, giving an unconditional statement about the actual group.
-/
noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
open Koszul Resonance LieComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (base : A.Complement)
attribute [local instance 3000]
  arrangementChenOriginalDegreeGroup arrangementChenOriginalDegreeMonoid
  arrangementChenOriginalDegreeScalars
local instance effectiveReductionOriginalFamilyFintype :
    Fintype (OriginalMaximalIsotropicFamily (cupQuotient A.rationalQuadraticKernel)) :=
  canonicalFamilyFintype ℂ (ι → ℂ) A.rationalQuadraticKernel
    A.rationalQuadraticKernel_all_maximal_cupQuotient_separated

private theorem effectiveReductionOriginalFamilyDimensionCount (m : ℕ) :
    Fintype.card {P : OriginalMaximalIsotropicFamily (cupQuotient A.rationalQuadraticKernel) //
      _root_.Module.finrank ℂ P.val = m} = A.singularProjectiveComponentDimensionCount m := by
  classical
  calc
    _ = A.rationalKernelQuotientDimensionCount m := by
      unfold rationalKernelQuotientDimensionCount originalMaximalIsotropicDimensionCount
      rfl
    _ = A.rationalMaximalIsotropicDimensionCount m :=
      A.rationalKernelQuotientDimensionCount_eq_original m
    _ = _ := (A.singularProjectiveComponentDimensionCount_eq_rational m).symm

/- Explicitly conditional: the effective actual Koszul bijection remains
a geometric proof obligation, not a project axiom or a final input. -/
set_option maxHeartbeats 800000 in
theorem actualRationalChenRanks_paperRange_of_originalCanonicalBijective
    (heffective : ∀ r : ℕ, Fintype.card ι - 3 ≤ r → Function.Bijective
      (originalCanonicalFamilyHomogeneousMap ℂ (ι → ℂ) A.rationalQuadraticKernel
        A.actualLogHolonomyLabelBasis.dualBasis r))
    (q : ℕ) (hq : max 2 (Fintype.card ι - 1) ≤ q) :
    A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal) := by
  have h2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hn : Fintype.card ι - 1 ≤ q := le_trans (le_max_right _ _) hq
  have hr : Fintype.card ι - 3 ≤ q - 2 := by omega
  have hH := originalCanonicalFamilyHomogeneous_counted_finrank_of_bijective
    ℂ (ι → ℂ) A.rationalQuadraticKernel
    A.rationalQuadraticKernel_all_maximal_cupQuotient_separated
    A.actualLogHolonomyLabelBasis.dualBasis (q - 2) (heffective (q - 2) hr)
  have hi : q - 1 = (q - 2) + 1 := by omega
  have hF : finiteChenRank (FundamentalGroup A.Complement base) (q - 1) =
      ∑ m ∈ Finset.range (Fintype.card ι + 1),
        A.singularProjectiveComponentDimensionCount m *
          ((q - 1) * (m + q - 2).choose q) := by
    rw [hi, A.actualFiniteChenRank_eq_originalKoszulDegree base (q - 2), hH,
      _root_.Module.finrank_fintype_fun_eq_card]
    apply Finset.sum_congr rfl
    intro m _hm
    rw [A.effectiveReductionOriginalFamilyDimensionCount m]
    have he : m + (q - 2) = m + q - 2 := by omega
    have hd : q - 2 + 2 = q := by omega
    rw [he, hd]
  change rationalChenRank (FundamentalGroup A.Complement base) (q - 1) = _
  rw [← finiteChenRank_eq_rationalChenRank, hF]
  exact congrArg (fun n : ℕ => (n : Cardinal))
    (A.actualResonanceChenRankExpression_eq_range q).symm

/-- The original-group endpoint is unconditional on the actual
low-dimensional boundary; no degree-map comparison is supplied. -/
theorem actualRationalChenRanks_allDegrees_of_atMostTwoHyperplanes
    (hN : Fintype.card ι ≤ 2) (q : ℕ) (hq : 2 ≤ q) :
    A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal) := by
  apply A.actualRationalChenRanks_paperRange_of_originalCanonicalBijective base
  · intro r _hr
    apply originalCanonicalFamilyHomogeneousMap_bijective_of_finrank_le_two
      ℂ (ι → ℂ) A.actualLogHolonomyLabelBasis.dualBasis A.rationalQuadraticKernel
    simpa only [_root_.Module.finrank_fintype_fun_eq_card] using hN
  · omega

end ChenRanks.AffineArrangement
