import Mathlib

/-!
# The actual group-theoretic objects underlying Chen ranks

The definitions in this file use the genuine maximal metabelian quotient
`G / G''`, the genuine lower central series, and its abelian successive
quotients.  Rational Chen ranks are the dimensions of the rationalizations
of those quotients.  They are not a synthetic sequence or a formula specified
in advance.

The zero-based indexing of mathlib's `lowerCentralSeries` is made explicit:
`lowerCentralPiece H k` is `Γ_(k+1)(H) / Γ_(k+2)(H)`.  Thus a usual Chen
degree `q + 1` uses `lowerCentralPiece (metabelianQuotient G) q`.

The accompanying `ArrangementObjects` module applies the construction to an
actual finite complex affine arrangement complement and its fundamental
group, defined from homotopy classes of loops.  This file proves the normality
and commutativity needed for the definitions.  It makes no claim that the
general Chen-rank formula, Orlik–Solomon theorem, formality, or the Chen–Koszul
comparison has already been formalized.
-/

noncomputable section

namespace ChenRanks

open scoped commutatorElement
open scoped TensorProduct

variable (G : Type*) [Group G]

/-- The actual maximal metabelian quotient `G/G''`. -/
def metabelianQuotient : Type _ := G ⧸ derivedSeries G 2

instance : Group (metabelianQuotient G) :=
  inferInstanceAs (Group (G ⧸ derivedSeries G 2))

/-- The quotient above really has trivial second derived subgroup. -/
theorem metabelianQuotient_second_derived :
    derivedSeries (metabelianQuotient G) 2 = ⊥ := by
  let f : G →* metabelianQuotient G := QuotientGroup.mk' (derivedSeries G 2)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  rw [← map_derivedSeries_eq hf]
  apply (Subgroup.map_eq_bot_iff (derivedSeries G 2)).mpr
  change derivedSeries G 2 ≤ (QuotientGroup.mk' (derivedSeries G 2)).ker
  rw [QuotientGroup.ker_mk']

/-- `Γ_(k+2)(G)` as a normal subgroup of `Γ_(k+1)(G)`.
Using a preimage under the subtype homomorphism supplies the precise subgroup
type required by a group quotient. -/
def nextLowerCentralIn (k : ℕ) : Subgroup (lowerCentralSeries G k) :=
  (lowerCentralSeries G (k + 1)).comap (lowerCentralSeries G k).subtype

instance nextLowerCentralIn_normal (k : ℕ) : (nextLowerCentralIn G k).Normal := by
  unfold nextLowerCentralIn
  infer_instance

/-- The numerator's internal commutator lies in the next lower central term. -/
theorem lowerCentral_internal_commutator_le (k : ℕ) :
    commutator (lowerCentralSeries G k) ≤ nextLowerCentralIn G k := by
  change commutator (lowerCentralSeries G k) ≤
    (lowerCentralSeries G (k + 1)).comap (lowerCentralSeries G k).subtype
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator]
  change ⁅lowerCentralSeries G k, lowerCentralSeries G k⁆ ≤
    ⁅lowerCentralSeries G k, (⊤ : Subgroup G)⁆
  exact Subgroup.commutator_mono le_rfl le_top

/-- The actual `(k+1)`st graded quotient of the lower central series. -/
def lowerCentralPiece (k : ℕ) : Type _ :=
  lowerCentralSeries G k ⧸ nextLowerCentralIn G k

instance (k : ℕ) : Group (lowerCentralPiece G k) :=
  inferInstanceAs (Group (lowerCentralSeries G k ⧸ nextLowerCentralIn G k))

/-- The lower central quotients are abelian; this is proved, not supplied
as a hypothesis. -/
instance lowerCentralPiece_commGroup (k : ℕ) : CommGroup (lowerCentralPiece G k) :=
  { (inferInstance : Group (lowerCentralPiece G k)) with
    mul_comm :=
      ((Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := nextLowerCentralIn G k)).mpr
          (lowerCentral_internal_commutator_le G k)).comm }

/-- The rationalized graded piece of the actual maximal metabelian quotient,
in ordinary Chen degree `k+1`. -/
abbrev rationalChenSpace (k : ℕ) :=
  ℚ ⊗[ℤ] Additive (lowerCentralPiece (metabelianQuotient G) k)

/-- Cardinal-valued rational Chen rank.  This retains infinite dimensions
for arbitrary groups and therefore does not silently turn them into zero. -/
def rationalChenRank (k : ℕ) : Cardinal :=
  Module.rank ℚ (rationalChenSpace G k)

/-- Natural-valued rank used when the actual Chen piece is finite dimensional.
The finiteness condition is explicit in the adjoining comparison theorem. -/
def finiteChenRank (k : ℕ) : ℕ :=
  Module.finrank ℚ (rationalChenSpace G k)

/-- For finite-dimensional actual Chen pieces, the natural and cardinal
rank definitions agree. -/
theorem finiteChenRank_eq_rationalChenRank (k : ℕ)
    [FiniteDimensional ℚ (rationalChenSpace G k)] :
    (finiteChenRank G k : Cardinal) = rationalChenRank G k :=
  Module.finrank_eq_rank ℚ (rationalChenSpace G k)

variable {G}

/-- Membership in the next term is the actual lower central membership test
in the ambient group. -/
@[simp] theorem mem_nextLowerCentralIn (k : ℕ) (x : lowerCentralSeries G k) :
    x ∈ nextLowerCentralIn G k ↔ (x : G) ∈ lowerCentralSeries G (k + 1) :=
  Iff.rfl

end ChenRanks
