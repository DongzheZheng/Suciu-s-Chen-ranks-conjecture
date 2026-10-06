import ChenRanks.FlagAssociatedGradedBracket
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Basic

/-!
# The actual associated Lie algebra of the raising-operator flag

The components are the actual operator subquotients J_q/(J_q ∩ J_(q+1)).
The bracket is induced by the actual associative endomorphism commutator.
The quotient construction proves representative independence. Here actual
direct-sum induction and the original ring identities prove alternation,
Jacobi and the native Lie structure. No bracket, Jacobi, finite flag or
comparison detector is supplied as an input.

The index q is the ordinary operator-raising degree. The original group
component n consequently maps to component q=n+1.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks.LieComparison

variable (k E : Type*) [Field k] [AddCommGroup E] [Module k E]
variable (F : ℕ → Submodule k E)

/-- Reindex the same actual current operator space. -/
def raisingCurrentReindex {q r : ℕ} (h : q = r) :
    degreeRaisingEndomorphisms k E F q ≃ₗ[k]
      degreeRaisingEndomorphisms k E F r := by
  cases h
  exact LinearEquiv.refl k _

@[simp] theorem raisingCurrentReindex_coe {q r : ℕ} (h : q = r)
    (a : degreeRaisingEndomorphisms k E F q) :
    (raisingCurrentReindex k E F h a : Module.End k E) = a := by
  cases h
  rfl

/-- Reindex the same actual successive quotient, without changing its
original operator representatives. -/
def raisingPieceReindex {q r : ℕ} (h : q = r) :
    DegreeRaisingPiece k E F q ≃ₗ[k] DegreeRaisingPiece k E F r := by
  cases h
  exact LinearEquiv.refl k _

@[simp] theorem raisingPieceReindex_mk {q r : ℕ} (h : q = r)
    (a : degreeRaisingEndomorphisms k E F q) :
    raisingPieceReindex k E F h ((nextDegreeRaisingWithin k E F q).mkQ a) =
      (nextDegreeRaisingWithin k E F r).mkQ (raisingCurrentReindex k E F h a) := by
  cases h
  rfl

/-- The actual direct sum of the actual operator layers. -/
abbrev flagAssociatedGraded := ⨁ q : ℕ, DegreeRaisingPiece k E F q

def flagGradedInclusion (q : ℕ) :
    DegreeRaisingPiece k E F q →ₗ[k] flagAssociatedGraded k E F :=
  DirectSum.lof k ℕ (DegreeRaisingPiece k E F) q

theorem flagGradedInclusion_reindex {q r : ℕ} (h : q = r)
    (x : DegreeRaisingPiece k E F q) :
    flagGradedInclusion k E F r (raisingPieceReindex k E F h x) =
      flagGradedInclusion k E F q x := by
  cases h
  rfl

theorem flagGradedInclusion_mk_reindex {q r : ℕ} (h : q = r)
    (a : degreeRaisingEndomorphisms k E F q) :
    flagGradedInclusion k E F r
        ((nextDegreeRaisingWithin k E F r).mkQ (raisingCurrentReindex k E F h a)) =
      flagGradedInclusion k E F q ((nextDegreeRaisingWithin k E F q).mkQ a) := by
  rw [← raisingPieceReindex_mk, flagGradedInclusion_reindex]

/-- The real direct-sum universal property extends the real quotient
commutator bilinearly. -/
def flagGradedBracket :
    flagAssociatedGraded k E F →ₗ[k]
      flagAssociatedGraded k E F →ₗ[k] flagAssociatedGraded k E F :=
  DirectSum.toModule k ℕ (flagAssociatedGraded k E F →ₗ[k] flagAssociatedGraded k E F)
    (fun q =>
      (DirectSum.toModule k ℕ
        (DegreeRaisingPiece k E F q →ₗ[k] flagAssociatedGraded k E F)
        (fun r => ((raisingPieceBracket k E F q r).compr₂
          (flagGradedInclusion k E F (q + r))).flip)).flip)

@[simp] theorem flagGradedBracket_inclusions (q r : ℕ)
    (x : DegreeRaisingPiece k E F q) (y : DegreeRaisingPiece k E F r) :
    flagGradedBracket k E F (flagGradedInclusion k E F q x)
        (flagGradedInclusion k E F r y) =
      flagGradedInclusion k E F (q + r) (raisingPieceBracket k E F q r x y) := by
  simp only [flagGradedBracket, flagGradedInclusion, DirectSum.toModule_lof,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

theorem raisingCurrentCommutator_swap (q r : ℕ)
    (a : degreeRaisingEndomorphisms k E F q)
    (b : degreeRaisingEndomorphisms k E F r) :
    raisingCurrentReindex k E F (Nat.add_comm r q)
      (raisingCommutatorBilinear k E F r q b a) =
      -(raisingCommutatorBilinear k E F q r a b) := by
  apply Subtype.ext
  rw [raisingCurrentReindex_coe]
  change (b : Module.End k E) * a - (a : Module.End k E) * b =
    -((a : Module.End k E) * b - (b : Module.End k E) * a)
  noncomm_ring

/-- Skew symmetry is proved on actual current representatives, then
extended to all genuine finite sums. -/
theorem flagGradedBracket_swap (x y : flagAssociatedGraded k E F) :
    flagGradedBracket k E F y x = -flagGradedBracket k E F x y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.add_apply, neg_add]
    exact congrArg₂ (· + ·) ih₁ ih₂
  | of q x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | add y₁ y₂ ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, neg_add]
      exact congrArg₂ (· + ·) ih₁ ih₂
    | of r y =>
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F q) x
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F r) y
      change flagGradedBracket k E F
        (flagGradedInclusion k E F r ((nextDegreeRaisingWithin k E F r).mkQ b))
        (flagGradedInclusion k E F q ((nextDegreeRaisingWithin k E F q).mkQ a)) =
          -flagGradedBracket k E F
            (flagGradedInclusion k E F q ((nextDegreeRaisingWithin k E F q).mkQ a))
            (flagGradedInclusion k E F r ((nextDegreeRaisingWithin k E F r).mkQ b))
      rw [flagGradedBracket_inclusions, flagGradedBracket_inclusions,
        raisingPieceBracket_mk_mk, raisingPieceBracket_mk_mk]
      have h := congrArg (fun c => flagGradedInclusion k E F (q + r)
        ((nextDegreeRaisingWithin k E F (q + r)).mkQ c))
        (raisingCurrentCommutator_swap k E F q r a b)
      dsimp only at h
      rw [flagGradedInclusion_mk_reindex, map_neg, map_neg] at h
      exact h

/-- Alternation holds without dividing by two, including characteristic
two, because the original ring commutator is alternating. -/
theorem flagGradedBracket_self (x : flagAssociatedGraded k E F) :
    flagGradedBracket k E F x x = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy, flagGradedBracket_swap k E F x y]
    abel
  | of q x =>
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F q) x
    change flagGradedBracket k E F
      (flagGradedInclusion k E F q ((nextDegreeRaisingWithin k E F q).mkQ a))
      (flagGradedInclusion k E F q ((nextDegreeRaisingWithin k E F q).mkQ a)) = 0
    rw [flagGradedBracket_inclusions, raisingPieceBracket_mk_mk]
    have hz : raisingCommutatorBilinear k E F q q a a = 0 := by
      apply Subtype.ext
      change (a : Module.End k E) * a - (a : Module.End k E) * a = 0
      exact sub_self _
    rw [hz, map_zero, map_zero]

/-- An actual nested current commutator at an actual common total degree. -/
def raisingCurrentJacobiTerm (q r s t : ℕ) (h : q + (r + s) = t)
    (a : degreeRaisingEndomorphisms k E F q)
    (b : degreeRaisingEndomorphisms k E F r)
    (c : degreeRaisingEndomorphisms k E F s) :
    degreeRaisingEndomorphisms k E F t :=
  raisingCurrentReindex k E F h
    (raisingCommutatorBilinear k E F q (r + s) a
      (raisingCommutatorBilinear k E F r s b c))

theorem raisingCurrentJacobiTerm_coe (q r s t : ℕ) (h : q + (r + s) = t)
    (a : degreeRaisingEndomorphisms k E F q)
    (b : degreeRaisingEndomorphisms k E F r)
    (c : degreeRaisingEndomorphisms k E F s) :
    (raisingCurrentJacobiTerm k E F q r s t h a b c : Module.End k E) =
      (a : Module.End k E) * ((b : Module.End k E) * c - (c : Module.End k E) * b) -
        ((b : Module.End k E) * c - (c : Module.End k E) * b) * a := by
  simp only [raisingCurrentJacobiTerm, raisingCurrentReindex_coe]
  rfl

/-- Associativity of the actual endomorphism ring proves the actual
current Jacobi identity before any quotient or direct sum is taken. -/
theorem raisingCurrentCommutator_jacobi (q r s : ℕ)
    (a : degreeRaisingEndomorphisms k E F q)
    (b : degreeRaisingEndomorphisms k E F r)
    (c : degreeRaisingEndomorphisms k E F s) :
    raisingCurrentJacobiTerm k E F q r s (q + r + s) (by omega) a b c +
      raisingCurrentJacobiTerm k E F r s q (q + r + s) (by omega) b c a +
      raisingCurrentJacobiTerm k E F s q r (q + r + s) (by omega) c a b = 0 := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_zero, raisingCurrentJacobiTerm_coe]
  noncomm_ring

private theorem flagGradedNestedBracket_representatives (q r s t : ℕ)
    (h : q + (r + s) = t)
    (a : degreeRaisingEndomorphisms k E F q)
    (b : degreeRaisingEndomorphisms k E F r)
    (c : degreeRaisingEndomorphisms k E F s) :
    flagGradedBracket k E F
      (flagGradedInclusion k E F q ((nextDegreeRaisingWithin k E F q).mkQ a))
      (flagGradedBracket k E F
        (flagGradedInclusion k E F r ((nextDegreeRaisingWithin k E F r).mkQ b))
        (flagGradedInclusion k E F s ((nextDegreeRaisingWithin k E F s).mkQ c))) =
    flagGradedInclusion k E F t ((nextDegreeRaisingWithin k E F t).mkQ
      (raisingCurrentJacobiTerm k E F q r s t h a b c)) := by
  rw [flagGradedBracket_inclusions, raisingPieceBracket_mk_mk,
    flagGradedBracket_inclusions, raisingPieceBracket_mk_mk]
  exact (flagGradedInclusion_mk_reindex k E F h _).symm

private def flagGradedJacobiSum (x y z : flagAssociatedGraded k E F) :=
  flagGradedBracket k E F x (flagGradedBracket k E F y z) +
    flagGradedBracket k E F y (flagGradedBracket k E F z x) +
    flagGradedBracket k E F z (flagGradedBracket k E F x y)

private theorem flagGradedJacobiSum_inclusions (q r s : ℕ)
    (x : DegreeRaisingPiece k E F q) (y : DegreeRaisingPiece k E F r)
    (z : DegreeRaisingPiece k E F s) :
    flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
      (flagGradedInclusion k E F r y) (flagGradedInclusion k E F s z) = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F q) x
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F r) y
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (nextDegreeRaisingWithin k E F s) z
  have h := congrArg (fun a => flagGradedInclusion k E F (q + r + s)
    ((nextDegreeRaisingWithin k E F (q + r + s)).mkQ a))
    (raisingCurrentCommutator_jacobi k E F q r s a b c)
  simp only [map_add, map_zero] at h
  unfold flagGradedJacobiSum
  rw [flagGradedNestedBracket_representatives k E F q r s (q + r + s) (by omega),
    flagGradedNestedBracket_representatives k E F r s q (q + r + s) (by omega),
    flagGradedNestedBracket_representatives k E F s q r (q + r + s) (by omega)]
  exact h

/-- Genuine ring Jacobi on actual representatives extends to all finite
sums in the actual associated graded operator space. -/
theorem flagGradedBracket_jacobi (x y z : flagAssociatedGraded k E F) :
    flagGradedBracket k E F x (flagGradedBracket k E F y z) +
      flagGradedBracket k E F y (flagGradedBracket k E F z x) +
      flagGradedBracket k E F z (flagGradedBracket k E F x y) = 0 := by
  change flagGradedJacobiSum k E F x y z = 0
  induction x using DirectSum.induction_on with
  | zero => simp only [flagGradedJacobiSum, map_zero, LinearMap.zero_apply, add_zero]
  | add x₁ x₂ ih₁ ih₂ =>
    have h : flagGradedJacobiSum k E F (x₁ + x₂) y z =
        flagGradedJacobiSum k E F x₁ y z + flagGradedJacobiSum k E F x₂ y z := by
      simp only [flagGradedJacobiSum, map_add, LinearMap.add_apply]
      abel
    rw [h, ih₁, ih₂, add_zero]
  | of q x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [flagGradedJacobiSum, map_zero, LinearMap.zero_apply, add_zero]
    | add y₁ y₂ ih₁ ih₂ =>
      change flagGradedJacobiSum k E F (flagGradedInclusion k E F q x) (y₁ + y₂) z = 0
      change flagGradedJacobiSum k E F (flagGradedInclusion k E F q x) y₁ z = 0 at ih₁
      change flagGradedJacobiSum k E F (flagGradedInclusion k E F q x) y₂ z = 0 at ih₂
      have h : flagGradedJacobiSum k E F (flagGradedInclusion k E F q x) (y₁ + y₂) z =
          flagGradedJacobiSum k E F (flagGradedInclusion k E F q x) y₁ z +
            flagGradedJacobiSum k E F (flagGradedInclusion k E F q x) y₂ z := by
        simp only [flagGradedJacobiSum, map_add, LinearMap.add_apply]
        abel
      rw [h, ih₁, ih₂, add_zero]
    | of r y =>
      induction z using DirectSum.induction_on with
      | zero => simp only [flagGradedJacobiSum, map_zero, LinearMap.zero_apply, add_zero]
      | add z₁ z₂ ih₁ ih₂ =>
        change flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
          (flagGradedInclusion k E F r y) (z₁ + z₂) = 0
        change flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
          (flagGradedInclusion k E F r y) z₁ = 0 at ih₁
        change flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
          (flagGradedInclusion k E F r y) z₂ = 0 at ih₂
        have h : flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
            (flagGradedInclusion k E F r y) (z₁ + z₂) =
            flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
              (flagGradedInclusion k E F r y) z₁ +
            flagGradedJacobiSum k E F (flagGradedInclusion k E F q x)
              (flagGradedInclusion k E F r y) z₂ := by
          simp only [flagGradedJacobiSum, map_add, LinearMap.add_apply]
          abel
        rw [h, ih₁, ih₂, add_zero]
      | of s z => exact flagGradedJacobiSum_inclusions k E F q r s x y z

private theorem cyclic_to_leibniz {M : Type*} [AddCommGroup M]
    (a b c : M) (h : a + -b + -c = 0) : a = c + b := by
  calc
    a = (a + -b + -c) + (c + b) := by abel
    _ = c + b := by rw [h, zero_add]

theorem flagGradedBracket_leibniz (x y z : flagAssociatedGraded k E F) :
    flagGradedBracket k E F x (flagGradedBracket k E F y z) =
      flagGradedBracket k E F (flagGradedBracket k E F x y) z +
        flagGradedBracket k E F y (flagGradedBracket k E F x z) := by
  have h := flagGradedBracket_jacobi k E F x y z
  rw [flagGradedBracket_swap k E F x z, map_neg,
    flagGradedBracket_swap k E F (flagGradedBracket k E F x y) z] at h
  exact cyclic_to_leibniz
    (flagGradedBracket k E F x (flagGradedBracket k E F y z))
    (flagGradedBracket k E F y (flagGradedBracket k E F x z))
    (flagGradedBracket k E F (flagGradedBracket k E F x y) z) h

instance flagAssociatedGradedLieRing : LieRing (flagAssociatedGraded k E F) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (⨁ q : ℕ, DegreeRaisingPiece k E F q))
  bracket x y := flagGradedBracket k E F x y
  add_lie x y z := LinearMap.congr_fun ((flagGradedBracket k E F).map_add x y) z
  lie_add x y z := (flagGradedBracket k E F x).map_add y z
  lie_self := flagGradedBracket_self k E F
  leibniz_lie := flagGradedBracket_leibniz k E F

instance flagAssociatedGradedLieAlgebra : LieAlgebra k (flagAssociatedGraded k E F) where
  toModule := inferInstanceAs (_root_.Module k (⨁ q : ℕ, DegreeRaisingPiece k E F q))
  lie_smul c x y := (flagGradedBracket k E F x).map_smul c y

/-- The native Lie bracket is the actual homogeneous quotient
commutator, in the true sum of physical raising degrees. -/
@[simp] theorem flagAssociatedGraded_lie_inclusions (q r : ℕ)
    (x : DegreeRaisingPiece k E F q) (y : DegreeRaisingPiece k E F r) :
    ⁅flagGradedInclusion k E F q x, flagGradedInclusion k E F r y⁆ =
      flagGradedInclusion k E F (q + r) (raisingPieceBracket k E F q r x y) :=
  flagGradedBracket_inclusions k E F q r x y

end ChenRanks.LieComparison
