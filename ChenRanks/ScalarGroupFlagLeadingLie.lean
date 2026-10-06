import ChenRanks.FlagAssociatedGradedLie
import ChenRanks.ScalarGroupAssociatedGraded

/-!
# The actual leading Lie map of an original flag representation

A genuine group representation whose actual deviations raise the actual
flag by one sends the original lower-central quotient of ordinary degree
n+1 into the actual operator layer J_(n+1)/J_(n+2). The original group-ring
identity proves preservation of the original commutator. Tensor and
direct-sum universal properties then give a genuine native scalar Lie
homomorphism, preserving every original degree.

The raising condition is an intermediate structural input for an actual
representation. There is no assumed leading bracket formula, injectivity,
monodromy, formality or Chen comparison. A concrete monodromy application
must derive this raising condition from its actual positive operators.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct DirectSum

namespace ChenRanks.LieComparison

variable (k G E : Type*) [Field k] [CharZero k] [Group G]
variable [AddCommGroup E] [Module k E]
variable (F : ℕ → Submodule k E) (hF : Antitone F)
variable (ρ : G →* (Module.End k E)ˣ)
variable (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
  degreeRaisingEndomorphisms k E F 1)

omit [CharZero k] in
/-- The already proved original representative commutator identity,
now in the actual native target direct sum. -/
theorem lowerCentralFlagLeading_bracket_representatives (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    flagGradedInclusion k E F ((m + n + 1) + 1)
      (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ (m + n + 1)
        (Additive.ofMul (lowerCentralPieceBracket G m n
          (QuotientGroup.mk' (nextLowerCentralIn G m) g)
          (QuotientGroup.mk' (nextLowerCentralIn G n) h)))) =
      ⁅flagGradedInclusion k E F (m + 1)
          (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ m
            (Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G m) g))),
        flagGradedInclusion k E F (n + 1)
          (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ n
            (Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G n) h)))⁆ := by
  rw [lowerCentralPieceFlagLeadingCharacter_bracket_mk_mk,
    lowerCentralPieceFlagLeadingCharacter_mk, lowerCentralPieceFlagLeadingCharacter_mk,
    flagAssociatedGraded_lie_inclusions, raisingPieceBracket_mk_mk]
  have hindex : (m + 1) + (n + 1) = (m + n + 1) + 1 := by omega
  have hrep : raisingCurrentReindex k E F hindex
      (raisingCommutatorBilinear k E F (m + 1) (n + 1)
        (lowerCentralFlagDifference k G E F hF ρ hρ m g)
        (lowerCentralFlagDifference k G E F hF ρ hρ n h)) =
      lowerCentralFlagCommutatorRepresentative k G E F hF ρ hρ m n g h := by
    apply Subtype.ext
    rw [raisingCurrentReindex_coe]
    rfl
  have hcast := flagGradedInclusion_mk_reindex k E F hindex
    (raisingCommutatorBilinear k E F (m + 1) (n + 1)
      (lowerCentralFlagDifference k G E F hF ρ hρ m g)
      (lowerCentralFlagDifference k G E F hF ρ hρ n h))
  rw [hrep] at hcast
  exact hcast

omit [CharZero k] in
/-- All original integral quotient classes retain their actual leading
commutator. No choice of original representative is supplied as input. -/
theorem lowerCentralFlagLeading_bracket (m n : ℕ)
    (a : Additive (lowerCentralPiece G m)) (b : Additive (lowerCentralPiece G n)) :
    flagGradedInclusion k E F ((m + n + 1) + 1)
      (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ (m + n + 1)
        (lowerCentralPieceBracketAdd G m n a b)) =
      ⁅flagGradedInclusion k E F (m + 1)
          (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ m a),
        flagGradedInclusion k E F (n + 1)
          (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ n b)⁆ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (nextLowerCentralIn G m) (Additive.toMul a)
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (nextLowerCentralIn G n) (Additive.toMul b)
  have hga : Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G m) g) = a :=
    congrArg Additive.ofMul hg
  have hhb : Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G n) h) = b :=
    congrArg Additive.ofMul hh
  rw [← hga, ← hhb]
  change flagGradedInclusion k E F ((m + n + 1) + 1)
      (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ (m + n + 1)
        (Additive.ofMul (lowerCentralPieceBracket G m n
          (QuotientGroup.mk' (nextLowerCentralIn G m) g)
          (QuotientGroup.mk' (nextLowerCentralIn G n) h)))) = _
  exact lowerCentralFlagLeading_bracket_representatives k G E F hF ρ hρ m n g h

omit [CharZero k] in
/-- The actual integral commutator formula extends through the original
tensor products in both variables. -/
theorem scalarLowerCentralFlagLeading_bracket (m n : ℕ)
    (x : scalarLowerCentralPiece k G m) (y : scalarLowerCentralPiece k G n) :
    flagGradedInclusion k E F ((m + n + 1) + 1)
      (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ (m + n + 1)
        (scalarLowerCentralPieceBracket k G m n x y)) =
      ⁅flagGradedInclusion k E F (m + 1)
          (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ m x),
        flagGradedInclusion k E F (n + 1)
          (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ n y)⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, zero_lie]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, add_lie, hx₁, hx₂]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, lie_zero]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, LieRing.lie_add, hy₁, hy₂]
    | tmul d b =>
      rw [scalarLowerCentralPieceBracket_tmul_tmul,
        scalarLowerCentralFlagLeadingMap_tmul,
        scalarLowerCentralFlagLeadingMap_tmul,
        scalarLowerCentralFlagLeadingMap_tmul,
        map_smul, map_smul, map_smul, smul_lie, lie_smul, smul_smul]
      exact congrArg (fun z : flagAssociatedGraded k E F => (c * d) • z)
        (lowerCentralFlagLeading_bracket k G E F hF ρ hρ m n a b)

/-- The actual direct-sum linear map retains the original ordinary
degree n+1 exactly in the actual physical operator layer n+1. -/
def scalarGroupFlagLeadingLinear :
    scalarGroupAssociatedGraded k G →ₗ[k] flagAssociatedGraded k E F :=
  (DirectSum.toModule k ℕ (flagAssociatedGraded k E F)
    (fun n => (flagGradedInclusion k E F (n + 1)).comp
      (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ n))).comp
    (scalarGroupGradedDirectSumEquiv k G).toLinearMap

@[simp] theorem scalarGroupFlagLeadingLinear_inclusion (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupFlagLeadingLinear k G E F hF ρ hρ
      (scalarGroupGradedInclusion k G n x) =
      flagGradedInclusion k E F (n + 1)
        (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ n x) := by
  change (DirectSum.toModule k ℕ (flagAssociatedGraded k E F)
    (fun n => (flagGradedInclusion k E F (n + 1)).comp
      (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ n)))
    ((scalarGroupGradedDirectSumEquiv k G) (scalarGroupGradedInclusion k G n x)) = _
  rw [scalarGroupGradedDirectSumEquiv_inclusion, DirectSum.toModule_lof,
    LinearMap.comp_apply]

/-- Preservation of the native Lie bracket is deduced from the genuine
original quotient formula by actual direct-sum induction. -/
theorem scalarGroupFlagLeadingLinear_lie
    (x y : scalarGroupAssociatedGraded k G) :
    scalarGroupFlagLeadingLinear k G E F hF ρ hρ ⁅x, y⁆ =
      ⁅scalarGroupFlagLeadingLinear k G E F hF ρ hρ x,
        scalarGroupFlagLeadingLinear k G E F hF ρ hρ y⁆ := by
  obtain ⟨x, rfl⟩ := (scalarGroupGradedDirectSumEquiv k G).symm.surjective x
  obtain ⟨y, rfl⟩ := (scalarGroupGradedDirectSumEquiv k G).symm.surjective y
  have hincl (n : ℕ) (z : scalarLowerCentralPiece k G n) :
      (scalarGroupGradedDirectSumEquiv k G).symm
        (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n z) =
      scalarGroupGradedInclusion k G n z := by
    apply (scalarGroupGradedDirectSumEquiv k G).injective
    rw [LinearEquiv.apply_symm_apply, scalarGroupGradedDirectSumEquiv_inclusion]
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_lie]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, add_lie, hx₁, hx₂]
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero =>
      simp only [map_zero]
      let a := (scalarGroupGradedDirectSumEquiv k G).symm
        (DirectSum.of (scalarLowerCentralPiece k G) m x)
      have hz : ⁅a, (0 : scalarGroupAssociatedGraded k G)⁆ = 0 :=
        (AddMonoidHom.mk' (fun z : scalarGroupAssociatedGraded k G => ⁅a, z⁆)
          (LieRing.lie_add a)).map_zero
      have htarget : ⁅scalarGroupFlagLeadingLinear k G E F hF ρ hρ a,
          (0 : flagAssociatedGraded k E F)⁆ = 0 :=
        (AddMonoidHom.mk' (fun z : flagAssociatedGraded k E F =>
          ⁅scalarGroupFlagLeadingLinear k G E F hF ρ hρ a, z⁆)
          (LieRing.lie_add _)).map_zero
      exact ((congrArg (scalarGroupFlagLeadingLinear k G E F hF ρ hρ) hz).trans
        (LinearMap.map_zero (scalarGroupFlagLeadingLinear k G E F hF ρ hρ))).trans
          htarget.symm
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, LieRing.lie_add, hy₁, hy₂]
    | of n y =>
      change scalarGroupFlagLeadingLinear k G E F hF ρ hρ
        ⁅(scalarGroupGradedDirectSumEquiv k G).symm
            (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x),
          (scalarGroupGradedDirectSumEquiv k G).symm
            (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n y)⁆ =
        ⁅scalarGroupFlagLeadingLinear k G E F hF ρ hρ
            ((scalarGroupGradedDirectSumEquiv k G).symm
              (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x)),
          scalarGroupFlagLeadingLinear k G E F hF ρ hρ
            ((scalarGroupGradedDirectSumEquiv k G).symm
              (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n y))⁆
      rw [hincl, hincl, scalarGroupAssociatedGraded_lie_inclusions,
        scalarGroupFlagLeadingLinear_inclusion,
        scalarGroupFlagLeadingLinear_inclusion,
        scalarGroupFlagLeadingLinear_inclusion]
      exact scalarLowerCentralFlagLeading_bracket k G E F hF ρ hρ m n x y

/-- The original scalar group associated Lie algebra has a genuine
degree-preserving native Lie morphism to the actual operator flag Lie
algebra. No injectivity or expected bracket behavior is assumed. -/
def scalarGroupFlagLeadingLieHom :
    scalarGroupAssociatedGraded k G →ₗ⁅k⁆ flagAssociatedGraded k E F where
  __ := scalarGroupFlagLeadingLinear k G E F hF ρ hρ
  map_lie' := fun {x y} => scalarGroupFlagLeadingLinear_lie k G E F hF ρ hρ x y

@[simp] theorem scalarGroupFlagLeadingLieHom_inclusion (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupFlagLeadingLieHom k G E F hF ρ hρ
      (scalarGroupGradedInclusion k G n x) =
      flagGradedInclusion k E F (n + 1)
        (scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ n x) := by
  change scalarGroupFlagLeadingLinear k G E F hF ρ hρ
    (scalarGroupGradedInclusion k G n x) = _
  exact scalarGroupFlagLeadingLinear_inclusion k G E F hF ρ hρ n x

end ChenRanks.LieComparison
