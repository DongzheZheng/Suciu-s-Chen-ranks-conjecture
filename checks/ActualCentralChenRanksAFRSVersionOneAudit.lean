import ChenRanks.CentralChenRanksAFRSVersionOne

/-!
# Central Chen-rank statements and foundational dependencies

The central theorem uses the same AFRS input as the affine theorem.
Its formulation uses the complement fundamental group and projective
resonance-component counts; the deconing label is chosen in the proof.
-/
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.universes true in
#check @ChenRanks.AffineArrangement.actualCentralDecone_resonanceChenRankExpression
set_option pp.universes true in
#check @ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperRange_versionOne
set_option pp.universes true in
#check @ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperSum_versionOne
#print axioms ChenRanks.AffineArrangement.actualCentralDecone_resonanceChenRankExpression
#print axioms ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperRange_versionOne
#print axioms ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperSum_versionOne

noncomputable section
open scoped BigOperators
open ChenRanks ChenRanks.AffineArrangement
universe u
example {d : ℕ} {ι : Type u} [Fintype ι] (A : AffineArrangement d ι)
    (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (hcentral : ∀ H, A.offset H = 0) (base : A.Complement)
    (q : ℕ) (hq : max 2 (Fintype.card ι - 2) ≤ q) :
    rationalChenRank (FundamentalGroup A.Complement base) (q - 1) =
      ((q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q : ℕ) := by
  change A.chenRank base (q - 1) = _
  exact A.actualCentralRationalChenRanks_paperSum_versionOne hAFRS hcentral base q hq
