import ChenRanks.AFRSEffectiveCanonicalDecompositionInput
import ChenRanks.ArrangementChenRanksEffectiveReduction

/-!
# Chen ranks of affine arrangements

For a finite complex affine arrangement, the Chen-rank formula holds in
its explicit stable range under the single AFRS effective decomposition
input. Both sides are defined from the complement: the rational rank of a
lower-central quotient of its maximal metabelian fundamental-group quotient,
and the dimensions of its projective resonance components.

Geometric separation, the Chen--Koszul comparison, finite-dimensionality,
and component counting are proved by the imported arrangement theory.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
universe u

theorem actualRationalChenRanks_paperRange_versionOne
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : AffineArrangement d ι)
    (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (base : A.Complement) (q : ℕ)
    (hq : max 2 (Fintype.card ι - 1) ≤ q) :
    A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal) := by
  by_cases hsmall : Fintype.card ι ≤ 2
  · exact A.actualRationalChenRanks_allDegrees_of_atMostTwoHyperplanes
      base hsmall q (le_trans (le_max_left _ _) hq)
  · apply A.actualRationalChenRanks_paperRange_of_originalCanonicalBijective base
    · intro r hr
      have hdim : 3 ≤ _root_.Module.finrank ℂ (ι → ℂ) := by
        simpa only [_root_.Module.finrank_fintype_fun_eq_card] using
          (show 3 ≤ Fintype.card ι by omega)
      have hrE : _root_.Module.finrank ℂ (ι → ℂ) - 3 ≤ r := by
        simpa only [_root_.Module.finrank_fintype_fun_eq_card] using hr
      exact hAFRS (ι → ℂ) A.rationalQuadraticKernel hdim
        (fun P hP hPdim => by
          simpa only [Resonance.cupQuotient, Submodule.ker_mkQ] using
            A.rationalQuadraticKernel_all_maximal_cupQuotient_separated P hP hPdim)
        (Fin (_root_.Module.finrank ℂ (ι → ℂ)))
        A.actualLogHolonomyLabelBasis.dualBasis r hrE
    · exact hq

end ChenRanks.AffineArrangement
