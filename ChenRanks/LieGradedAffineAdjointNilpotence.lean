import Mathlib.Algebra.Lie.Graded
import Mathlib.LinearAlgebra.Span.Defs
import ChenRanks.LieDerivationAffineAdjoint

/-!
# Actual graded tails and nilpotence of the actual affine adjoints

The tail submodule is the actual span of the actual homogeneous pieces
of degree at least n. Native graded brackets prove its bracket law.
Positivity and an actual finite degree bound then prove nilpotence of
every actual affine adjoint. Neither an abstract raising operator, an
assumed nilpotent representation, nor an exponential inverse is supplied.

The positive finite grading is an intermediate structural input. The
grading of each actual finite holonomy truncation remains to be derived
from that actual quotient, before using this as an arrangement conclusion.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The actual span of all original homogeneous pieces in degrees at least n. -/
def nativeGradedTail (n : ℕ) : Submodule k L :=
  Submodule.span k {x | ∃ i : ℕ, n ≤ i ∧ x ∈ ℒ i}

omit [GradedLieAlgebra ℒ] in
theorem mem_nativeGradedTail_of_mem (n i : ℕ) (x : L)
    (hi : n ≤ i) (hx : x ∈ ℒ i) : x ∈ nativeGradedTail k L ℒ n :=
  Submodule.subset_span ⟨i, hi, hx⟩

omit [GradedLieAlgebra ℒ] in
theorem nativeGradedTail_antitone (m n : ℕ) (hmn : m ≤ n) :
    nativeGradedTail k L ℒ n ≤ nativeGradedTail k L ℒ m := by
  apply Submodule.span_mono
  rintro x ⟨i, hi, hx⟩
  exact ⟨i, hmn.trans hi, hx⟩

/-- The actual graded bracket extends to the actual span, without a
filtration-bracket premise. -/
theorem lie_mem_nativeGradedTail (n m : ℕ) (x y : L)
    (hx : x ∈ nativeGradedTail k L ℒ n)
    (hy : y ∈ nativeGradedTail k L ℒ m) :
    ⁅x, y⁆ ∈ nativeGradedTail k L ℒ (n + m) := by
  refine Submodule.span_induction₂
    (p := fun a b _ _ => ⁅a, b⁆ ∈ nativeGradedTail k L ℒ (n + m))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro a b ⟨i, hi, hai⟩ ⟨j, hj, hbj⟩
    exact mem_nativeGradedTail_of_mem k L ℒ (n + m) (i + j) ⁅a, b⁆
      (Nat.add_le_add hi hj) (SetLike.GradedBracket.bracket_mem rfl hai hbj)
  · intro y _
    rw [zero_lie]
    exact Submodule.zero_mem _
  · intro x _
    rw [lie_zero]
    exact Submodule.zero_mem _
  · intro x y z _ _ _ hxz hyz
    rw [add_lie]
    exact Submodule.add_mem _ hxz hyz
  · intro x y z _ _ _ hxy hxz
    rw [lie_add]
    exact Submodule.add_mem _ hxy hxz
  · intro a x y _ _ hxy
    rw [smul_lie]
    exact Submodule.smul_mem _ a hxy
  · intro a x y _ _ hxy
    rw [lie_smul]
    exact Submodule.smul_mem _ a hxy

/-- A genuinely positive native decomposition is entirely in its first tail. -/
theorem nativeGradedTail_one_eq_top (hzero : ℒ 0 = ⊥) :
    nativeGradedTail k L ℒ 1 = ⊤ := by
  apply top_unique
  intro x _
  exact DirectSum.Decomposition.inductionOn ℒ
    (Submodule.zero_mem _)
    (fun {i} a => by
      by_cases hi : i = 0
      · subst i
        have ha : (a : L) = 0 := by
          simpa only [hzero, Submodule.mem_bot] using a.property
        rw [ha]
        exact Submodule.zero_mem _
      · exact mem_nativeGradedTail_of_mem k L ℒ 1 i a (Nat.one_le_iff_ne_zero.mpr hi)
          a.property)
    (fun a b ha hb => Submodule.add_mem _ ha hb) x

omit [GradedLieAlgebra ℒ] in
/-- The actual tail vanishes above an actual finite degree bound. -/
theorem nativeGradedTail_eq_bot_of_bound (c n : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) (hcn : c < n) :
    nativeGradedTail k L ℒ n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨i, hi, hx⟩
  rw [hbound i (hcn.trans_le hi)] at hx
  exact hx

/-- The genuine affine operator's first coordinate is zero after one step. -/
theorem derivationAffineAdjointEnd_pow_succ_fst_eq_zero
    (D : LieDerivation k L L) (x : L) (n : ℕ) (p : k × L) :
    (((derivationAffineAdjointEnd k L D x) ^ (n + 1)) p).1 = 0 := by
  rw [pow_succ']
  change (derivationAffineAdjointEnd k L D x
    (((derivationAffineAdjointEnd k L D x) ^ n) p)).1 = 0
  rfl

/-- Successive genuine affine adjoints move the original coordinate to
successive actual tails. The first step kills the scalar coordinate. -/
theorem derivationAffineAdjointEnd_pow_succ_snd_mem
    (hzero : ℒ 0 = ⊥) (D : LieDerivation k L L) (x : L)
    (n : ℕ) (p : k × L) :
    (((derivationAffineAdjointEnd k L D x) ^ (n + 1)) p).2 ∈
      nativeGradedTail k L ℒ (n + 1) := by
  induction n with
  | zero =>
    rw [nativeGradedTail_one_eq_top k L ℒ hzero]
    trivial
  | succ n ih =>
    rw [pow_succ']
    change (((derivationAffineAdjointEnd k L D x) ^ (n + 1)) p).1 • D x +
      ⁅x, (((derivationAffineAdjointEnd k L D x) ^ (n + 1)) p).2⁆ ∈ _
    rw [derivationAffineAdjointEnd_pow_succ_fst_eq_zero]
    simp only [zero_smul, zero_add]
    have hx : x ∈ nativeGradedTail k L ℒ 1 := by
      rw [nativeGradedTail_one_eq_top k L ℒ hzero]
      trivial
    simpa only [Nat.add_comm 1 (n + 1)] using
      lie_mem_nativeGradedTail k L ℒ 1 (n + 1) x _ hx ih

/-- Nilpotence of the actual affine representation is derived from the
actual finite positive grading, not supplied as a representation property. -/
theorem derivationAffineAdjointEnd_isNilpotent_of_positive_finite_grading
    (hzero : ℒ 0 = ⊥) (c : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x : L) :
    IsNilpotent (derivationAffineAdjointEnd k L D x) := by
  refine ⟨c + 1, ?_⟩
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · exact derivationAffineAdjointEnd_pow_succ_fst_eq_zero k L D x c p
  · have h := derivationAffineAdjointEnd_pow_succ_snd_mem k L ℒ hzero D x c p
    rw [nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 1) hbound (Nat.lt_succ_self c)] at h
    exact h

end ChenRanks.LieComparison
