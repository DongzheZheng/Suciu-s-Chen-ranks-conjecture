import ChenRanks.GroupAssociatedGradedLie
import Mathlib.Algebra.Lie.Solvable

/-!
# Actual metabelianity of the original Chen associated Lie algebra

The vanishing of the original group's second derived subgroup kills
original commutators of commutators. Original quotient, tensor, and
direct-sum induction transport that identity to the actual graded Lie
algebra. Actual native Lie derived ideals are then handled by their
proved linear-span description. No metabelian Lie structure, vanishing
detector, formality, or Chen comparison is an input.
-/

noncomputable section

open scoped commutatorElement TensorProduct DirectSum

namespace ChenRanks

variable (G : Type*) [Group G]

/-- This is an identity in the original group, derived from its actual
second derived subgroup. -/
theorem group_commutators_commutator_eq_one_of_second_derived
    (hD : derivedSeries G 2 = ⊥) (x y z w : G) :
    ⁅⁅x, y⁆, ⁅z, w⁆⁆ = 1 := by
  have hxy : ⁅x, y⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hzw : ⁅z, w⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top z) (Subgroup.mem_top w)
  have hd : ⁅⁅x, y⁆, ⁅z, w⁆⁆ ∈ derivedSeries G 2 :=
    Subgroup.commutator_mem_commutator hxy hzw
  rw [hD] at hd
  exact Subgroup.mem_bot.mp hd

/-- Four real quotient inductions preserve the original double
commutator, which is genuinely zero in every actual target quotient. -/
theorem lowerCentralPieceBracket_commutators_eq_one
    (hD : derivedSeries G 2 = ⊥) (m n p q : ℕ)
    (x : lowerCentralPiece G m) (y : lowerCentralPiece G n)
    (z : lowerCentralPiece G p) (w : lowerCentralPiece G q) :
    lowerCentralPieceBracket G (m + n + 1) (p + q + 1)
      (lowerCentralPieceBracket G m n x y)
      (lowerCentralPieceBracket G p q z w) = 1 := by
  refine QuotientGroup.induction_on x fun x => ?_
  refine QuotientGroup.induction_on y fun y => ?_
  refine QuotientGroup.induction_on z fun z => ?_
  refine QuotientGroup.induction_on w fun w => ?_
  change lowerCentralPieceBracket G (m + n + 1) (p + q + 1)
      (lowerCentralPieceBracket G m n
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)
        (QuotientGroup.mk' (nextLowerCentralIn G n) y))
      (lowerCentralPieceBracket G p q
        (QuotientGroup.mk' (nextLowerCentralIn G p) z)
        (QuotientGroup.mk' (nextLowerCentralIn G q) w)) = 1
  rw [lowerCentralPieceBracket_mk_mk, lowerCentralPieceBracket_mk_mk,
    lowerCentralPieceBracket_mk_mk]
  apply lowerCentralPieceAmbientHom_injective G ((m + n + 1) + (p + q + 1) + 1)
  rw [lowerCentralPieceAmbientHom_mk, map_one]
  change QuotientGroup.mk'
      (lowerCentralSeries G ((m + n + 1) + (p + q + 1) + 1 + 1))
      ⁅⁅(x : G), (y : G)⁆, ⁅(z : G), (w : G)⁆⁆ = 1
  rw [group_commutators_commutator_eq_one_of_second_derived G hD, map_one]

theorem lowerCentralPieceBracketAdd_commutators_eq_zero
    (hD : derivedSeries G 2 = ⊥) (m n p q : ℕ)
    (x : Additive (lowerCentralPiece G m)) (y : Additive (lowerCentralPiece G n))
    (z : Additive (lowerCentralPiece G p)) (w : Additive (lowerCentralPiece G q)) :
    lowerCentralPieceBracketAdd G (m + n + 1) (p + q + 1)
      (lowerCentralPieceBracketAdd G m n x y)
      (lowerCentralPieceBracketAdd G p q z w) = 0 := by
  change Additive.ofMul (lowerCentralPieceBracket G (m + n + 1) (p + q + 1)
      (lowerCentralPieceBracket G m n (Additive.toMul x) (Additive.toMul y))
      (lowerCentralPieceBracket G p q (Additive.toMul z) (Additive.toMul w))) = 0
  exact congrArg Additive.ofMul
    (lowerCentralPieceBracket_commutators_eq_one G hD m n p q
      (Additive.toMul x) (Additive.toMul y) (Additive.toMul z) (Additive.toMul w))

/-- Actual scalar extension, with all four variables checked by
actual tensor induction rather than a new compatibility premise. -/
theorem rationalLowerCentralPieceBracket_commutators_eq_zero
    (hD : derivedSeries G 2 = ⊥) (m n p q : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) (w : rationalLowerCentralPiece G q) :
    rationalLowerCentralPieceBracket G (m + n + 1) (p + q + 1)
      (rationalLowerCentralPieceBracket G m n x y)
      (rationalLowerCentralPieceBracket G p q z w) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.add_apply, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y₁ y₂ ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂, add_zero]
    | tmul b y =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add z₁ z₂ ih₁ ih₂ =>
        simp only [map_add, LinearMap.add_apply, ih₁, ih₂, add_zero]
      | tmul c z =>
        induction w using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | add w₁ w₂ ih₁ ih₂ =>
          simp only [map_add, LinearMap.add_apply, ih₁, ih₂, add_zero]
        | tmul d w =>
          rw [rationalLowerCentralPieceBracket_tmul_tmul,
            rationalLowerCentralPieceBracket_tmul_tmul,
            rationalLowerCentralPieceBracket_tmul_tmul,
            lowerCentralPieceBracketAdd_commutators_eq_zero G hD,
            TensorProduct.tmul_zero]

/-- The same original identity holds on all finite sums in the
actual native direct sum. -/
theorem rationalGroupAssociatedGraded_commutators_eq_zero
    (hD : derivedSeries G 2 = ⊥)
    (x y z w : rationalGroupAssociatedGraded G) :
    ⁅⁅x, y⁆, ⁅z, w⁆⁆ = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_lie]
  | add x₁ x₂ ih₁ ih₂ => rw [add_lie, add_lie, ih₁, ih₂, add_zero]
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [lie_zero, zero_lie]
    | add y₁ y₂ ih₁ ih₂ => rw [lie_add, add_lie, ih₁, ih₂, add_zero]
    | of n y =>
      induction z using DirectSum.induction_on with
      | zero => simp only [zero_lie, lie_zero]
      | add z₁ z₂ ih₁ ih₂ => rw [add_lie, lie_add, ih₁, ih₂, add_zero]
      | of p z =>
        induction w using DirectSum.induction_on with
        | zero => simp only [lie_zero]
        | add w₁ w₂ ih₁ ih₂ => rw [lie_add, lie_add, ih₁, ih₂, add_zero]
        | of q w =>
          change ⁅⁅rationalGroupGradedInclusion G m x,
            rationalGroupGradedInclusion G n y⁆,
              ⁅rationalGroupGradedInclusion G p z,
                rationalGroupGradedInclusion G q w⁆⁆ = 0
          rw [rationalGroupAssociatedGraded_lie_inclusions,
            rationalGroupAssociatedGraded_lie_inclusions,
            rationalGroupAssociatedGraded_lie_inclusions,
            rationalLowerCentralPieceBracket_commutators_eq_zero G hD, map_zero]

/-- Native Lie ideal spans promote the original four-element
identity to actual metabelianity of the original associated Lie algebra. -/
theorem rationalGroupAssociatedGraded_second_derived_eq_bot
    (hD : derivedSeries G 2 = ⊥) :
    LieAlgebra.derivedSeries ℚ (rationalGroupAssociatedGraded G) 2 = ⊥ := by
  apply le_bot_iff.mp
  change ⁅LieAlgebra.derivedSeries ℚ (rationalGroupAssociatedGraded G) 1,
    LieAlgebra.derivedSeries ℚ (rationalGroupAssociatedGraded G) 1⁆ ≤ ⊥
  rw [LieSubmodule.lie_le_iff]
  intro x hx y hy
  rw [LieSubmodule.mem_bot]
  change x ∈ (↑⁅(⊤ : LieIdeal ℚ (rationalGroupAssociatedGraded G)),
    (⊤ : LieIdeal ℚ (rationalGroupAssociatedGraded G))⁆ :
      Submodule ℚ (rationalGroupAssociatedGraded G)) at hx
  change y ∈ (↑⁅(⊤ : LieIdeal ℚ (rationalGroupAssociatedGraded G)),
    (⊤ : LieIdeal ℚ (rationalGroupAssociatedGraded G))⁆ :
      Submodule ℚ (rationalGroupAssociatedGraded G)) at hy
  rw [LieIdeal.toLieSubalgebra_toSubmodule,
    LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _ha, b, _hb, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, _hc, d, _hd, rfl⟩ := hy
      exact rationalGroupAssociatedGraded_commutators_eq_zero G hD a b c d
    | zero => exact lie_zero _
    | add y₁ y₂ _hy₁ _hy₂ ih₁ ih₂ => rw [lie_add, ih₁, ih₂, add_zero]
    | smul c y _hy ih => rw [lie_smul, ih, smul_zero]
  | zero => exact zero_lie _
  | add x₁ x₂ _hx₁ _hx₂ ih₁ ih₂ => rw [add_lie, ih₁, ih₂, add_zero]
  | smul c x _hx ih => rw [smul_lie, ih, smul_zero]

/-- Final specialization uses the already proved second derived
subgroup vanishing of the actual original `G/G''`. There is no remaining
metabelianity hypothesis. -/
theorem rationalChenAssociatedGraded_second_derived_eq_bot :
    LieAlgebra.derivedSeries ℚ (rationalChenAssociatedGraded G) 2 = ⊥ :=
  rationalGroupAssociatedGraded_second_derived_eq_bot (metabelianQuotient G)
    (metabelianQuotient_second_derived G)

theorem rationalChenAssociatedGraded_commutators_eq_zero
    (x y z w : rationalChenAssociatedGraded G) : ⁅⁅x, y⁆, ⁅z, w⁆⁆ = 0 :=
  rationalGroupAssociatedGraded_commutators_eq_zero (metabelianQuotient G)
    (metabelianQuotient_second_derived G) x y z w

end ChenRanks
