import ChenRanks.ScalarGroupAssociatedGraded
import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Physical Euler weights of the actual original group lower-central quotients

The original native group term with index n is ordinary degree n+1.
The genuine scalar/direct-sum equivalence defines an actual linear
endomorphism with that physical weight on that same original quotient.
The actual group commutator formula proves the derivation identity.
Characteristic zero separates its weights, so its actual eigenspace of
weight q>0 is exactly the actual inclusion of the original quotient
Gamma_q/Gamma_(q+1) tensor k. The weight-zero eigenspace is zero.

This is not a definition of the original lower-central filtration or
of its dimensions. No model/Chen comparison or homogeneous-preservation
condition is supplied. This file is an uncompiled candidate.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (k : Type*) [Field k] [CharZero k]
variable (G : Type*) [Group G]

private theorem actualGroupNativeLieRightZero (x : scalarGroupAssociatedGraded k G) :
    ⁅x, (0 : scalarGroupAssociatedGraded k G)⁆ = 0 :=
  (AddMonoidHom.mk' (fun y : scalarGroupAssociatedGraded k G => ⁅x, y⁆)
    (LieRing.lie_add x)).map_zero

private theorem actualGroupNativeLieSmul (c : k) (x y : scalarGroupAssociatedGraded k G) :
    ⁅x, c • y⁆ = c • ⁅x, y⁆ :=
  LieAlgebra.lie_smul (R := k) (L := scalarGroupAssociatedGraded k G) c x y

private theorem actualGroupNativeSmulLie (c : k) (x y : scalarGroupAssociatedGraded k G) :
    ⁅c • x, y⁆ = c • ⁅x, y⁆ := by
  rw [← lie_skew (c • x) y, actualGroupNativeLieSmul,
    ← lie_skew x y, smul_neg]

/-- The genuine projection onto the same original scalarized
successive group quotient. -/
def scalarGroupPieceProjection (n : ℕ) :
    scalarGroupAssociatedGraded k G →ₗ[k] scalarLowerCentralPiece k G n :=
  (DirectSum.component k ℕ (scalarLowerCentralPiece k G) n).comp
    (scalarGroupGradedDirectSumEquiv k G).toLinearMap

@[simp] theorem scalarGroupPieceProjection_inclusion_self (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupPieceProjection k G n (scalarGroupGradedInclusion k G n x) = x := by
  change DirectSum.component k ℕ (scalarLowerCentralPiece k G) n
    ((scalarGroupGradedDirectSumEquiv k G) (scalarGroupGradedInclusion k G n x)) = x
  rw [scalarGroupGradedDirectSumEquiv_inclusion, DirectSum.component.lof_self]

/-- The actual physical weight is ordinary degree n+1, retaining
the original group-series convention at every index. -/
def scalarGroupPhysicalEulerLinear :
    Module.End k (scalarGroupAssociatedGraded k G) :=
  (DirectSum.toModule k ℕ (scalarGroupAssociatedGraded k G)
    (fun n => ((n + 1 : ℕ) : k) • scalarGroupGradedInclusion k G n)).comp
      (scalarGroupGradedDirectSumEquiv k G).toLinearMap

@[simp] theorem scalarGroupPhysicalEulerLinear_inclusion (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupPhysicalEulerLinear k G (scalarGroupGradedInclusion k G n x) =
      ((n + 1 : ℕ) : k) • scalarGroupGradedInclusion k G n x := by
  change (DirectSum.toModule k ℕ (scalarGroupAssociatedGraded k G)
    (fun n => ((n + 1 : ℕ) : k) • scalarGroupGradedInclusion k G n))
      ((scalarGroupGradedDirectSumEquiv k G) (scalarGroupGradedInclusion k G n x)) = _
  rw [scalarGroupGradedDirectSumEquiv_inclusion, DirectSum.toModule_lof,
    LinearMap.smul_apply]

/-- The original commutator has physical degree (m+1)+(n+1),
so the actual physical Euler operator obeys the actual Leibniz rule. -/
theorem scalarGroupPhysicalEulerLinear_lie
    (x y : scalarGroupAssociatedGraded k G) :
    scalarGroupPhysicalEulerLinear k G ⁅x, y⁆ =
      ⁅x, scalarGroupPhysicalEulerLinear k G y⁆ +
        ⁅scalarGroupPhysicalEulerLinear k G x, y⁆ := by
  obtain ⟨x, rfl⟩ := (scalarGroupGradedDirectSumEquiv k G).symm.surjective x
  obtain ⟨y, rfl⟩ := (scalarGroupGradedDirectSumEquiv k G).symm.surjective y
  have hincl (n : ℕ) (a : scalarLowerCentralPiece k G n) :
      (scalarGroupGradedDirectSumEquiv k G).symm
        (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n a) =
      scalarGroupGradedInclusion k G n a := by
    apply (scalarGroupGradedDirectSumEquiv k G).injective
    rw [LinearEquiv.apply_symm_apply, scalarGroupGradedDirectSumEquiv_inclusion]
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_lie, add_zero]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, add_lie, hx₁, hx₂]
    abel
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero =>
      simp only [map_zero]
      rw [actualGroupNativeLieRightZero, actualGroupNativeLieRightZero,
        LinearMap.map_zero, add_zero]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, LieRing.lie_add, hy₁, hy₂]
      abel
    | of n y =>
      change scalarGroupPhysicalEulerLinear k G
          ⁅(scalarGroupGradedDirectSumEquiv k G).symm
              (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x),
            (scalarGroupGradedDirectSumEquiv k G).symm
              (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n y)⁆ =
        ⁅(scalarGroupGradedDirectSumEquiv k G).symm
            (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x),
          scalarGroupPhysicalEulerLinear k G
            ((scalarGroupGradedDirectSumEquiv k G).symm
              (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n y))⁆ +
        ⁅scalarGroupPhysicalEulerLinear k G
            ((scalarGroupGradedDirectSumEquiv k G).symm
              (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x)),
          (scalarGroupGradedDirectSumEquiv k G).symm
            (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) n y)⁆
      rw [hincl, hincl, scalarGroupAssociatedGraded_lie_inclusions,
        scalarGroupPhysicalEulerLinear_inclusion,
        scalarGroupPhysicalEulerLinear_inclusion,
        scalarGroupPhysicalEulerLinear_inclusion, actualGroupNativeLieSmul,
        actualGroupNativeSmulLie,
        scalarGroupAssociatedGraded_lie_inclusions, ← add_smul]
      congr 1
      push_cast
      ring

/-- A native derivation on the original actual group-associated Lie
algebra, proved from its true group commutator. -/
def scalarGroupPhysicalEulerDerivation :
    LieDerivation k (scalarGroupAssociatedGraded k G) (scalarGroupAssociatedGraded k G) where
  __ := scalarGroupPhysicalEulerLinear k G
  leibniz' x y := by
    rw [scalarGroupPhysicalEulerLinear_lie, sub_eq_add_neg,
      lie_skew (scalarGroupPhysicalEulerLinear k G x) y]

@[simp] theorem scalarGroupPhysicalEulerDerivation_inclusion (n : ℕ)
    (x : scalarLowerCentralPiece k G n) :
    scalarGroupPhysicalEulerDerivation k G (scalarGroupGradedInclusion k G n x) =
      ((n + 1 : ℕ) : k) • scalarGroupGradedInclusion k G n x :=
  scalarGroupPhysicalEulerLinear_inclusion k G n x

/-- Each actual homogeneous projection measures its same actual
physical Euler weight on every original element. -/
theorem scalarGroupPieceProjection_euler (n : ℕ)
    (x : scalarGroupAssociatedGraded k G) :
    scalarGroupPieceProjection k G n (scalarGroupPhysicalEulerLinear k G x) =
      ((n + 1 : ℕ) : k) • scalarGroupPieceProjection k G n x := by
  obtain ⟨x, rfl⟩ := (scalarGroupGradedDirectSumEquiv k G).symm.surjective x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | of m x =>
    have hincl : (scalarGroupGradedDirectSumEquiv k G).symm
        (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x) =
        scalarGroupGradedInclusion k G m x := by
      apply (scalarGroupGradedDirectSumEquiv k G).injective
      rw [LinearEquiv.apply_symm_apply, scalarGroupGradedDirectSumEquiv_inclusion]
    change scalarGroupPieceProjection k G n (scalarGroupPhysicalEulerLinear k G
        ((scalarGroupGradedDirectSumEquiv k G).symm
          (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x))) =
      ((n + 1 : ℕ) : k) • scalarGroupPieceProjection k G n
        ((scalarGroupGradedDirectSumEquiv k G).symm
          (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) m x))
    rw [hincl, scalarGroupPhysicalEulerLinear_inclusion, map_smul]
    change ((m + 1 : ℕ) : k) •
        DirectSum.component k ℕ (scalarLowerCentralPiece k G) n
          ((scalarGroupGradedDirectSumEquiv k G) (scalarGroupGradedInclusion k G m x)) =
      ((n + 1 : ℕ) : k) •
        DirectSum.component k ℕ (scalarLowerCentralPiece k G) n
          ((scalarGroupGradedDirectSumEquiv k G) (scalarGroupGradedInclusion k G m x))
    rw [scalarGroupGradedDirectSumEquiv_inclusion, DirectSum.component.of]
    by_cases h : m = n
    · subst m
      rfl
    · simp only [dif_neg h, smul_zero]

/-- Distinct actual physical weights have genuinely disjoint
eigenspaces; the proof uses characteristic-zero scalar cancellation. -/
theorem scalarGroupPieceProjection_zero_of_eigenvector (q n : ℕ)
    (x : scalarGroupAssociatedGraded k G)
    (hx : scalarGroupPhysicalEulerLinear k G x = (q : k) • x)
    (hn : n + 1 ≠ q) : scalarGroupPieceProjection k G n x = 0 := by
  have he := congrArg (scalarGroupPieceProjection k G n) hx
  rw [scalarGroupPieceProjection_euler, map_smul] at he
  have hw : (((n + 1 : ℕ) : k) - (q : k)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hn
  have hz : ((((n + 1 : ℕ) : k) - (q : k)) •
      scalarGroupPieceProjection k G n x) = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hw

/-- A positive-weight eigenvector lies in the actual original
Gamma_q/Gamma_(q+1) scalarized quotient, with its actual projection as
representative. This is the precise physical-degree endpoint. -/
theorem scalarGroup_eigenvector_eq_original_inclusion (q : ℕ) (hq : 1 ≤ q)
    (x : scalarGroupAssociatedGraded k G)
    (hx : scalarGroupPhysicalEulerLinear k G x = (q : k) • x) :
    x = scalarGroupGradedInclusion k G (q - 1)
      (scalarGroupPieceProjection k G (q - 1) x) := by
  apply (scalarGroupGradedDirectSumEquiv k G).injective
  rw [scalarGroupGradedDirectSumEquiv_inclusion]
  apply DirectSum.ext_component (R := k) (ι := ℕ) (M := scalarLowerCentralPiece k G)
  intro n
  change scalarGroupPieceProjection k G n x =
    DirectSum.component k ℕ (scalarLowerCentralPiece k G) n
      (DirectSum.lof k ℕ (scalarLowerCentralPiece k G) (q - 1)
        (scalarGroupPieceProjection k G (q - 1) x))
  by_cases h : q - 1 = n
  · subst n
    rw [DirectSum.component.lof_self]
  · rw [DirectSum.component.of, dif_neg h]
    exact scalarGroupPieceProjection_zero_of_eigenvector k G q n x hx (by omega)

/-- The actual zero-weight eigenspace is zero, including groups with
zero first quotient. -/
theorem scalarGroup_zero_eigenvector_eq_zero
    (x : scalarGroupAssociatedGraded k G)
    (hx : scalarGroupPhysicalEulerLinear k G x = 0) : x = 0 := by
  apply (scalarGroupGradedDirectSumEquiv k G).injective
  rw [map_zero]
  apply DirectSum.ext_component (R := k) (ι := ℕ) (M := scalarLowerCentralPiece k G)
  intro n
  change scalarGroupPieceProjection k G n x = 0
  exact scalarGroupPieceProjection_zero_of_eigenvector k G 0 n x
    (by simpa only [Nat.cast_zero, zero_smul] using hx) (by omega)

end ChenRanks
