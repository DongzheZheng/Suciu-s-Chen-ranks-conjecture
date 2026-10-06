import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-! A genuine affine adjoint representation constructed from a native
Lie derivation. Its bracket law follows from native Jacobi and the native
derivation identity. An injective derivation makes the representation
faithful. No faithful-representation, positive-grading, Euler, PBW, BCH,
monodromy, completion, or formality premise is supplied or concluded.
The injectivity criterion is an intermediate theorem; its use for Euler
derivations requires a separate actual grading and injectivity proof.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L]

def derivationAffineAdjointEnd (D : LieDerivation k L L) (x : L) :
    Module.End k (k × L) where
  toFun p := (0, p.1 • D x + ⁅x, p.2⁆)
  map_add' p q := by
    apply Prod.ext
    · simp only [Prod.fst_add, zero_add]
    · change (p.1 + q.1) • D x + ⁅x, p.2 + q.2⁆ =
        (p.1 • D x + ⁅x, p.2⁆) + (q.1 • D x + ⁅x, q.2⁆)
      rw [add_smul, lie_add]
      abel
  map_smul' c p := by
    apply Prod.ext
    · change (0 : k) = c • (0 : k)
      simp only [smul_zero]
    · change (c * p.1) • D x + ⁅x, c • p.2⁆ =
        c • (p.1 • D x + ⁅x, p.2⁆)
      rw [lie_smul, smul_add, smul_smul]

/-- The actual block operators form a genuine native Lie homomorphism. -/
def derivationAffineAdjoint (D : LieDerivation k L L) :
    L →ₗ⁅k⁆ Module.End k (k × L) where
  toFun := derivationAffineAdjointEnd k L D
  map_add' x y := by
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · change (0 : k) = 0 + 0
      simp only [zero_add]
    · change p.1 • D (x + y) + ⁅x + y, p.2⁆ =
        (p.1 • D x + ⁅x, p.2⁆) + (p.1 • D y + ⁅y, p.2⁆)
      rw [map_add, smul_add, add_lie]
      abel
  map_smul' c x := by
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · change (0 : k) = c • (0 : k)
      simp only [smul_zero]
    · change p.1 • D (c • x) + ⁅c • x, p.2⁆ =
        c • (p.1 • D x + ⁅x, p.2⁆)
      rw [map_smul, smul_lie, smul_add, smul_comm]
  map_lie' {x y} := by
    rw [LieRing.of_associative_ring_bracket]
    apply LinearMap.ext
    intro p
    simp only [LinearMap.sub_apply, Module.End.mul_apply, derivationAffineAdjointEnd]
    apply Prod.ext
    · change (0 : k) = 0 - 0
      simp only [sub_self]
    · simp only [Prod.snd_sub]
      change p.1 • D ⁅x, y⁆ + ⁅⁅x, y⁆, p.2⁆ =
        ((0 : k) • D x + ⁅x, p.1 • D y + ⁅y, p.2⁆⁆) -
          ((0 : k) • D y + ⁅y, p.1 • D x + ⁅x, p.2⁆⁆)
      simp only [zero_smul, zero_add]
      rw [LieDerivation.apply_lie_eq_sub, smul_sub, lie_lie,
        lie_add, lie_add, lie_smul, lie_smul]
      abel

/-- Faithfulness is genuinely detected on the original vector `(1,0)`. -/
theorem derivationAffineAdjoint_injective (D : LieDerivation k L L)
    (hD : Function.Injective D) : Function.Injective (derivationAffineAdjoint k L D) := by
  intro x y hxy
  apply hD
  have h := congrArg (fun f : Module.End k (k × L) => (f (1, 0)).2) hxy
  change (1 : k) • D x + ⁅x, (0 : L)⁆ =
    (1 : k) • D y + ⁅y, (0 : L)⁆ at h
  simpa only [one_smul, lie_zero, add_zero] using h

end ChenRanks.LieComparison
