import ChenRanks.ChenAbelianFactorRanks

/-! Genuine Chen-space transport by an actual group equivalence.
Both the metabelian quotient and every lower-central quotient retain
their original definitions. No Chen-rank equality is assumed. -/

noncomputable section

namespace ChenRanks

variable {G H : Type*} [Group G] [Group H]

/-- The original group equivalence induces an actual equivalence of
the genuine maximal metabelian quotients. -/
def metabelianGroupEquiv (e : G ≃* H) :
    metabelianQuotient G ≃* metabelianQuotient H :=
  QuotientGroup.congr (derivedSeries G 2) (derivedSeries H 2) e
    (map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 2)

/-- Genuine rationalized Chen-space transport induced by the original
group equivalence, in every original zero-based degree. -/
def rationalChenSpaceEquiv (e : G ≃* H) (n : ℕ) :
    rationalChenSpace G n ≃ₗ[ℚ] rationalChenSpace H n :=
  ((lowerCentralPieceEquiv (metabelianGroupEquiv e) n).toAdditive.toIntLinearEquiv).baseChange
    ℤ ℚ _ _

end ChenRanks
