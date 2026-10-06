import ChenRanks.LieEulerEigenvectors
import ChenRanks.LieDerivationNativeExtension

/-!
# Actual positive native automorphisms fixing the actual Euler axis

The actual bracket with the actual axis forces the image of a genuine
homogeneous vector to have the same genuine Euler weight. Its scalar
coordinate vanishes because the degree is nonzero. The actual raising
condition and actual next-tail intersection then force the original
vector to be fixed. Native decomposition supplies all original vectors.

The raising condition describes the actual automorphism being classified;
it is not an automorphism-classification or bijectivity premise. This
file does not yet show that an actual connection's parallel transport has
that condition, or classify automorphisms whose axis is not fixed.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]

/-- The actual native axis bracket, for every actual extension vector. -/
theorem nativeDerivationExtensionAxis_bracket_coordinates
    (D : LieDerivation k L L) (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionCoordinates k L D ⁅nativeDerivationExtensionAxis k L D, p⁆ =
      (0, -D p.left) := by
  apply Prod.ext
  · change ⁅(1 : k), p.right⁆ = 0
    simp [Ring.lie_def, mul_comm]
  · change ⁅(0 : L), p.left⁆ + (-(1 • D)) p.left - (-(p.right • D)) 0 = -D p.left
    simp only [zero_lie, one_smul, LieDerivation.neg_apply, LieDerivation.smul_apply,
      map_zero, smul_zero, neg_zero, sub_zero, zero_add]

variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- Fixing the actual axis imposes the actual degree on every homogeneous image. -/
theorem nativeEulerFixedAxis_image_coordinates
    (hzero : ℒ 0 = ⊥)
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (haxis : T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)) =
      nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ))
    (n : ℕ) (w : L) (hw : w ∈ ℒ n)
    (hraise : (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w))).2 - w ∈
        nativeGradedTail k L ℒ (n + 1)) :
    nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w)) = (0, w) := by
  by_cases hn : n = 0
  · subst n
    have hwzero : w = 0 := by rw [hzero] at hw; exact hw
    rw [hwzero]
    change nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (T (0 : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) = (0, 0)
    rw [map_zero]
    rfl
  · let D := nativeEulerDerivation k L ℒ
    let e := nativeDerivationExtensionCoordinates k L D
    let p := T (nativeDerivationExtensionOriginal k L D w)
    have hbracket : ⁅nativeDerivationExtensionAxis k L D,
        nativeDerivationExtensionOriginal k L D w⁆ =
        nativeDerivationExtensionOriginal k L D (-D w) := by
      apply e.injective
      rw [nativeDerivationExtensionAxis_bracket_original]
      rfl
    have hmap := congrArg e (T.map_lie (nativeDerivationExtensionAxis k L D)
      (nativeDerivationExtensionOriginal k L D w))
    rw [hbracket, haxis, nativeDerivationExtensionAxis_bracket_coordinates] at hmap
    rw [nativeEulerDerivation_of_mem k L ℒ n w hw] at hmap
    simp only [map_neg, map_smul] at hmap
    change -((n : k) • e p) = (0, -D (e p).2) at hmap
    have hfirst := congrArg Prod.fst hmap
    change -((n : k) * (e p).1) = 0 at hfirst
    have hfirstzero : (e p).1 = 0 :=
      (mul_eq_zero.mp (neg_eq_zero.mp hfirst)).resolve_left (Nat.cast_ne_zero.mpr hn)
    have hsecond := congrArg Prod.snd hmap
    change -((n : k) • (e p).2) = -D (e p).2 at hsecond
    have heigen : D (e p).2 = (n : k) • (e p).2 := (neg_inj.mp hsecond).symm
    have hhom : (e p).2 ∈ ℒ n := nativeEuler_eigenvector_mem_homogeneous k L ℒ n _ heigen
    have hzeroDifference : (e p).2 - w = 0 :=
      eq_zero_of_homogeneous_mem_next_tail k L ℒ n _
        ((ℒ n).sub_mem hhom hw) hraise
    apply Prod.ext
    · exact hfirstzero
    · exact sub_eq_zero.mp hzeroDifference

/-- A genuine positive native automorphism fixing the genuine Euler
axis is the identity; no scalar-quotient condition is supplied. -/
theorem nativeEulerPositiveAutomorphism_eq_refl_of_fixed_axis
    (hzero : ℒ 0 = ⊥)
    (T : NativeDerivationExtension k L (nativeEulerDerivation k L ℒ) ≃ₗ⁅k⁆
      NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (haxis : T (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)) =
      nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ))
    (hraise : ∀ (n : ℕ) (w : L), w ∈ ℒ n →
      (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
        (T (nativeDerivationExtensionOriginal k L (nativeEulerDerivation k L ℒ) w))).2 - w ∈
          nativeGradedTail k L ℒ (n + 1)) :
    T = LieEquiv.refl := by
  let D := nativeEulerDerivation k L ℒ
  let e := nativeDerivationExtensionCoordinates k L D
  have hOriginal : ∀ w : L, T (nativeDerivationExtensionOriginal k L D w) =
      nativeDerivationExtensionOriginal k L D w := by
    refine DirectSum.Decomposition.inductionOn ℒ (motive := fun w =>
      T (nativeDerivationExtensionOriginal k L D w) =
        nativeDerivationExtensionOriginal k L D w) ?_ ?_ ?_
    · change T (0 : NativeDerivationExtension k L D) = 0
      exact map_zero T
    · intro n w
      apply e.injective
      exact nativeEulerFixedAxis_image_coordinates k L ℒ hzero T haxis n w
        w.property (hraise n w w.property)
    · intro a b ha hb
      rw [map_add, map_add, ha, hb]
  apply LieEquiv.ext
  intro p
  change T p = p
  have hp : p = p.right • nativeDerivationExtensionAxis k L D +
      nativeDerivationExtensionOriginal k L D p.left := by
    apply e.injective
    change (p.right, p.left) = (p.right * 1 + 0, p.right • (0 : L) + p.left)
    simp only [mul_one, add_zero, smul_zero, zero_add]
  calc
    T p = T (p.right • nativeDerivationExtensionAxis k L D +
      nativeDerivationExtensionOriginal k L D p.left) := congrArg T hp
    _ = p.right • nativeDerivationExtensionAxis k L D +
      nativeDerivationExtensionOriginal k L D p.left := by rw [map_add, map_smul, haxis, hOriginal]
    _ = p := hp.symm

end ChenRanks.LieComparison
