import ChenRanks.CentralChenRanksAFRSVersionOne

/-!
# Main statements and foundational dependencies

This file displays the single AFRS input and the affine and central
Chen-rank formulas. The examples identify the formulas with the rational
lower-central ranks of the complement fundamental group and with the
projective resonance-component counts. The final commands display the
foundational axioms of the checked declarations.
-/
noncomputable section
open scoped BigOperators TensorProduct
open ChenRanks ChenRanks.Koszul ChenRanks.Resonance
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs false
universe u

#print ChenRanks.Koszul.AFRSEffectiveCanonicalDecomposition
#check @ChenRanks.AffineArrangement.actualRationalChenRanks_paperRange_versionOne
#check @ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperRange_versionOne

/-- The black-box parameter has exactly the original canonical-map
statement, with no Chen comparison or component-count premise. -/
example : AFRSEffectiveCanonicalDecomposition.{u} ↔
    ∀ (E : Type u) [AddCommGroup E] [_root_.Module ℂ E] [FiniteDimensional ℂ E]
      (I : Submodule ℂ (⋀[ℂ]^2 E)),
      3 ≤ _root_.Module.finrank ℂ E →
      (∀ P : Submodule ℂ E,
        IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
        2 ≤ _root_.Module.finrank ℂ P →
        mixedExterior P ⊓ LinearMap.ker (cupQuotient I) = pureExterior P) →
      ∀ (τ : Type) [Fintype τ]
        (b : _root_.Module.Basis τ ℂ (_root_.Module.Dual ℂ E)) (r : ℕ),
        _root_.Module.finrank ℂ E - 3 ≤ r →
        Function.Bijective (originalCanonicalFamilyHomogeneousMap ℂ E I b r) :=
  Iff.rfl

namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type u} [Fintype ι] (A : AffineArrangement d ι)

/-- The original rank definition retains its cardinal value. -/
example (base : A.Complement) (q : ℕ) :
    A.chenRank base (q - 1) =
      _root_.Module.rank ℚ
        (ℚ ⊗[ℤ] Additive
          (lowerCentralPiece
            (metabelianQuotient (FundamentalGroup A.Complement base)) (q - 1))) := rfl

/-- Affine effective formula, with the literal original group quotient
and literal actual component sum exposed in the conclusion. -/
example (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (base : A.Complement) (q : ℕ)
    (hq : max 2 (Fintype.card ι - 1) ≤ q) :
    _root_.Module.rank ℚ
        (ℚ ⊗[ℤ] Additive
          (lowerCentralPiece
            (metabelianQuotient (FundamentalGroup A.Complement base)) (q - 1))) =
      (((q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q : ℕ) : Cardinal) := by
  change A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal)
  exact A.actualRationalChenRanks_paperRange_versionOne hAFRS base q hq

/-- Central effective formula has no chosen decone hyperplane among
its hypotheses. The input is only the same AFRS proposition. -/
example (hAFRS : Koszul.AFRSEffectiveCanonicalDecomposition.{u})
    (hcentral : ∀ H, A.offset H = 0) (base : A.Complement) (q : ℕ)
    (hq : max 2 (Fintype.card ι - 2) ≤ q) :
    _root_.Module.rank ℚ
        (ℚ ⊗[ℤ] Additive
          (lowerCentralPiece
            (metabelianQuotient (FundamentalGroup A.Complement base)) (q - 1))) =
      (((q - 1) * ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        A.singularProjectiveComponentDimensionCount m * (m + q - 2).choose q : ℕ) : Cardinal) := by
  change A.chenRank base (q - 1) = (A.actualResonanceChenRankExpression q : Cardinal)
  exact A.actualCentralRationalChenRanks_paperRange_versionOne hAFRS hcentral base q hq

end ChenRanks.AffineArrangement

-- Source provenance: actual cardinal rank, proved finite-rank comparison,
-- original Koszul degree and native projective component counts.
#print ChenRanks.rationalChenRank
#print ChenRanks.finiteChenRank
#print ChenRanks.AffineArrangement.chenRank
#print ChenRanks.AffineArrangement.actualResonanceChenRankExpression
#print ChenRanks.AffineArrangement.singularProjectiveComponentDimensionCount
#check @ChenRanks.finiteChenRank_eq_rationalChenRank
#check @ChenRanks.AffineArrangement.actualRationalChenPiece_finiteDimensional
#check @ChenRanks.AffineArrangement.actualFiniteChenRank_eq_originalKoszulDegree
#check @ChenRanks.AffineArrangement.singularProjectiveComponentDimensionCount_eq_rational
#check @ChenRanks.AffineArrangement.actualCentralDecone_resonanceChenRankExpression

-- These queries traverse the proof constants. A local hypothesis hAFRS
-- cannot appear as an added axiom in this transitive declaration audit.
#print axioms ChenRanks.Koszul.AFRSEffectiveCanonicalDecomposition
#print axioms ChenRanks.AffineArrangement.actualRationalChenRanks_paperRange_versionOne
#print axioms ChenRanks.AffineArrangement.actualCentralRationalChenRanks_paperRange_versionOne
#print axioms ChenRanks.finiteChenRank_eq_rationalChenRank
#print axioms ChenRanks.AffineArrangement.actualRationalChenPiece_finiteDimensional
#print axioms ChenRanks.AffineArrangement.actualFiniteChenRank_eq_originalKoszulDegree
#print axioms ChenRanks.AffineArrangement.singularProjectiveComponentDimensionCount_eq_rational
#print axioms ChenRanks.AffineArrangement.actualResonanceChenRankExpression_eq_range
#print axioms ChenRanks.AffineArrangement.actualCentralDecone_resonanceChenRankExpression
