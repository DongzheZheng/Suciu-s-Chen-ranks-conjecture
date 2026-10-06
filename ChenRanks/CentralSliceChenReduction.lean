import ChenRanks.CentralSliceDeconing
import ChenRanks.FundamentalGroupTopologicalGroup
import ChenRanks.ChenGroupEquivalences

/-!
# Actual central-arrangement Chen-space reduction to its original slice

The actual complement-slice homeomorphism induces the genuine fundamental
group product equivalence. The actual nonzero complex scalars are a
topological group, whose genuine fundamental group at the actual scale
basepoint is abelian by the proved translation argument. Its factor can
therefore be removed from the genuine rationalized lower-central quotients
of the maximal metabelian quotient in every Chen degree at least two.

The lower-dimensional affine-coordinate realization and resonance-component
comparison of this slice remain separate steps of the manuscript.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)

/-- The actual central complement group is the genuine product group
at the original normalized point and original scale. -/
def centralComplementGroupEquiv (x : A.Complement) :
    A.complementGroup x ≃*
      FundamentalGroup (A.CentralSliceComplement i₀) (A.centralSlicePoint hcentral i₀ x) ×
        FundamentalGroup ℂˣ (A.centralScale hcentral i₀ x) :=
  (fundamentalGroupHomeomorphEquiv (A.centralComplementSliceHomeomorph hcentral i₀) x).trans
    (fundamentalGroupProductEquiv (A.CentralSliceComplement i₀) ℂˣ
      (A.centralSlicePoint hcentral i₀ x) (A.centralScale hcentral i₀ x))

/-- The original central arrangement's genuine rational Chen space
equals the original slice's genuine space in ordinary Chen degree `n+2`.
No topology, model, group-product or rank-comparison hypothesis is supplied. -/
def centralComplementChenSpaceSuccEquiv (x : A.Complement) (n : ℕ) :
    rationalChenSpace (A.complementGroup x) (n + 1) ≃ₗ[ℚ]
      rationalChenSpace
        (FundamentalGroup (A.CentralSliceComplement i₀) (A.centralSlicePoint hcentral i₀ x))
        (n + 1) :=
  (rationalChenSpaceEquiv (A.centralComplementGroupEquiv hcentral i₀ x) (n + 1)).trans
    (rationalChenProductSuccEquiv
      (FundamentalGroup (A.CentralSliceComplement i₀) (A.centralSlicePoint hcentral i₀ x))
      (FundamentalGroup ℂˣ (A.centralScale hcentral i₀ x)) n)

/-- The actual cardinal-valued Chen ranks agree, without an unproved
finiteness premise or a conversion of infinite dimensions to zero. -/
theorem centralComplementChenRank_succ (x : A.Complement) (n : ℕ) :
    A.chenRank x (n + 1) =
      rationalChenRank
        (FundamentalGroup (A.CentralSliceComplement i₀) (A.centralSlicePoint hcentral i₀ x))
        (n + 1) :=
  (A.centralComplementChenSpaceSuccEquiv hcentral i₀ x n).rank_eq

end ChenRanks.AffineArrangement
