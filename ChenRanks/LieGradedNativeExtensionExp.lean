import ChenRanks.LieGradedAffineAdjointNilpotence
import ChenRanks.LieDerivationNativeExtensionExp

/-!
# The genuine native exponential from an actual finite positive grading

The native coordinate operator is compared to the actual affine adjoint
by its already constructed coordinate formula. Its nilpotence comes from
the actual finite positive grading. Native conjugation transports that
proved nilpotence to the original semidirect extension; its true native
exponential is therefore defined without a nilpotence premise.

This does not yet construct the actual holonomy truncation or identify
all positive unipotent automorphisms with these exponentials.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]

/-- The actual native coordinate formula is the actual original affine
adjoint operator, rather than an arbitrary faithful representation. -/
theorem nativeDerivationExtensionAdjointCoordinateEnd_eq_affine
    (D : LieDerivation k L L) (x : L) :
    nativeDerivationExtensionAdjointCoordinateEnd k L D x =
      derivationAffineAdjointEnd k L D x := by
  apply LinearMap.ext
  intro p
  rw [nativeDerivationExtensionAdjointCoordinateEnd_apply]
  rfl

variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The nilpotence required by native Lie exponentiation is genuinely
derived from the actual finite positive grading. -/
theorem nativeDerivationExtensionAdjoint_isNilpotent_of_positive_finite_grading
    (hzero : ℒ 0 = ⊥) (c : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x : L) :
    IsNilpotent (nativeDerivationExtensionAdjoint k L D x).toLinearMap := by
  have h := derivationAffineAdjointEnd_isNilpotent_of_positive_finite_grading
    k L ℒ hzero c hbound D x
  rw [← nativeDerivationExtensionAdjointCoordinateEnd_eq_affine k L D x] at h
  have hh := h.map (nativeDerivationExtensionCoordinates k L D).conjRingEquiv.symm
  simpa only [nativeDerivationExtensionAdjointCoordinateEnd,
    RingEquiv.symm_apply_apply] using hh

/-- A true native Lie automorphism constructed from actual grading data.
Its existence is a conclusion; no automorphism or nilpotence is supplied. -/
def nativePositiveFiniteGradingExponential
    (hzero : ℒ 0 = ⊥) (c : ℕ)
    (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
    (D : LieDerivation k L L) (x : L) :
    NativeDerivationExtension k L D ≃ₗ⁅k⁆ NativeDerivationExtension k L D :=
  nativeDerivationExtensionExponential k L D x
    (nativeDerivationExtensionAdjoint_isNilpotent_of_positive_finite_grading
      k L ℒ hzero c hbound D x)

end ChenRanks.LieComparison
