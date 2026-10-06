import ChenRanks.CentralChenRanksAFRSVersionOne

/-!
# The effective Chen-rank formula

The two theorems below give the rational Chen ranks of the complement's
fundamental group in terms of its intrinsic resonance-component counts.
Both take the AFRS effective canonical decomposition as their sole
external mathematical input. Separation and the group, cohomology,
component-counting and deconing comparisons are proved in the imported
theory.
-/

noncomputable section
open scoped BigOperators
namespace ChenRanks.AffineArrangement
universe u
variable {d : ℕ} {ι : Type u} [Fintype ι] (A : AffineArrangement d ι)

/-- The Chen-rank formula for a finite complex affine arrangement.
The index `q - 1` represents ordinary Chen degree `q`. -/
theorem chenRanks_affine
    (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (base : A.Complement) (q : ℕ)
    (hq : max 2 (Fintype.card ι - 1) ≤ q) :
    A.chenRank base (q - 1) =
      ((q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q : ℕ) := by
  simpa only [actualResonanceChenRankExpression] using
    A.actualRationalChenRanks_paperRange_versionOne hAFRS base q hq

/-- The improved stable range for a central arrangement.
The deconing hyperplane, when needed, is chosen within the proof. -/
theorem chenRanks_central
    (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (hcentral : ∀ H, A.offset H = 0)
    (base : A.Complement) (q : ℕ)
    (hq : max 2 (Fintype.card ι - 2) ≤ q) :
    A.chenRank base (q - 1) =
      ((q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q : ℕ) :=
  A.actualCentralRationalChenRanks_paperSum_versionOne hAFRS hcentral base q hq

end ChenRanks.AffineArrangement
