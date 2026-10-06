import ChenRanks.LieEulerAxisInverse
import ChenRanks.LieGradedNativeExtensionExp

/-!
# The constructed Euler-axis polynomial is the actual native exponential

The original finite Lie polynomial is identified with the original native
finite exponential on the original semidirect axis. The factorial scalars
come from the actual restricted rational action, not an identification of
unrelated exponentials. This is the comparison required before the
constructed inverse can classify actual positive automorphisms.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- Actual powers on the actual axis give exactly the original nested Lie brackets. -/
theorem nativeEulerAxisIterate_eq_affine_power (x : L) (n : ℕ) :
    (((derivationAffineAdjointEnd k L (nativeEulerDerivation k L ℒ) x) ^ (n + 1))
      (1, 0)).2 = nativeEulerAxisIterate k L ℒ x n := by
  induction n with
  | zero =>
    rw [pow_one]
    change 1 • nativeEulerDerivation k L ℒ x + ⁅x, (0 : L)⁆ =
      nativeEulerDerivation k L ℒ x
    rw [one_smul, lie_zero, add_zero]
  | succ n ih =>
    rw [pow_succ']
    change (((derivationAffineAdjointEnd k L (nativeEulerDerivation k L ℒ) x) ^
      (n + 1)) (1, 0)).1 • nativeEulerDerivation k L ℒ x +
      ⁅x, (((derivationAffineAdjointEnd k L (nativeEulerDerivation k L ℒ) x) ^
        (n + 1)) (1, 0)).2⁆ = _
    rw [derivationAffineAdjointEnd_pow_succ_fst_eq_zero, zero_smul, zero_add, ih]
    rfl

/-- The actual known bound permits the actual native exponential sum
to be taken through degree c+1, including its actual zero final term. -/
theorem nativeEulerAffineAdjoint_pow_c_add_two_eq_zero
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) (x : L) :
    (derivationAffineAdjointEnd k L (nativeEulerDerivation k L ℒ) x) ^ (c + 2) = 0 := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · exact derivationAffineAdjointEnd_pow_succ_fst_eq_zero
      k L (nativeEulerDerivation k L ℒ) x (c + 1) p
  · have h := derivationAffineAdjointEnd_pow_succ_snd_mem
      k L ℒ hzero (nativeEulerDerivation k L ℒ) x (c + 1) p
    rw [nativeGradedTail_eq_bot_of_bound k L ℒ c (c + 2) hbound (by omega)] at h
    exact h

private theorem rational_end_smul_apply_snd
    (q : ℚ) (f : Module.End k (k × L)) (p : k × L) :
    ((q • f) p).2 = (algebraMap ℚ k q) • (f p).2 := by
  change ((algebraMap ℚ k q) • f p).2 = _
  rfl

private theorem end_sum_apply_snd {α : Type*}
    (s : Finset α) (f : α → Module.End k (k × L)) (p : k × L) :
    ((∑ i ∈ s, f i) p).2 = ∑ i ∈ s, (f i p).2 := by
  change (LinearMap.snd k k L) ((∑ i ∈ s, f i) p) = _
  rw [LinearMap.sum_apply, map_sum]
  rfl

/-- The actual native rational exponential gives the same actual finite
Lie polynomial whose inverse has already been constructed. -/
theorem nativeEulerAffineExponential_axis_snd
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) (x : L) :
    (IsNilpotent.exp (derivationAffineAdjointEnd k L (nativeEulerDerivation k L ℒ) x)
      (1, 0)).2 = nativeEulerAxisDisplacement k L ℒ c x := by
  rw [IsNilpotent.exp_eq_sum
    (nativeEulerAffineAdjoint_pow_c_add_two_eq_zero k L ℒ hzero c hbound x),
    end_sum_apply_snd]
  rw [Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply, add_zero]
  unfold nativeEulerAxisDisplacement
  apply Finset.sum_congr rfl
  intro n _
  rw [rational_end_smul_apply_snd, nativeEulerAxisIterate_eq_affine_power]
  congr 1
  simp only [map_inv₀, map_natCast]

/-- The actual native Lie automorphism on the actual native axis has
the actual polynomial displacement, with actual nilpotence derived. -/
theorem nativePositiveFiniteGradingExponential_axis_displacement
    (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥) (x : L) :
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (nativePositiveFiniteGradingExponential k L ℒ hzero c hbound
        (nativeEulerDerivation k L ℒ) x
        (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).2 =
      nativeEulerAxisDisplacement k L ℒ c x := by
  unfold nativePositiveFiniteGradingExponential
  rw [nativeDerivationExtensionExponential_coordinates,
    nativeDerivationExtensionAdjointCoordinateEnd_eq_affine]
  exact nativeEulerAffineExponential_axis_snd k L ℒ hzero c hbound x

end ChenRanks.LieComparison
