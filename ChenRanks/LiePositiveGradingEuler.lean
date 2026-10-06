import Mathlib.Algebra.Lie.Graded
import ChenRanks.LieDerivationAffineAdjoint

/-!
# The actual native Euler derivation of an actual positive grading

The grading is the native `GradedLieAlgebra`, with its actual direct-sum
decomposition and actual graded bracket. Its Euler derivation is the
native `LieDerivation.ofGrading`. The inverse weights define a genuine
linear operator on that same direct sum. The actual zero degree being
zero gives a left inverse, hence injectivity and a faithful affine adjoint.

This is an intermediate grading theorem. The actual holonomy quotient's
grading, its actual finite truncations, nilpotence of its adjoints, and
monodromy have to be constructed separately; none is inferred here from
the arrangement H1 or cup comparison.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

/-- The true native derivation multiplies each actual degree by that degree. -/
def nativeEulerDerivation : LieDerivation k L L :=
  LieDerivation.ofGrading ℒ (Nat.castAddMonoidHom k)

omit [CharZero k] in
/-- Its action on a genuine homogeneous element follows from the native
grading constructor, rather than a supplied Euler formula. -/
theorem nativeEulerDerivation_of_mem (i : ℕ) (a : L) (ha : a ∈ ℒ i) :
    nativeEulerDerivation k L ℒ a = (i : k) • a :=
  LieDerivation.ofGrading_apply_apply ℒ (Nat.castAddMonoidHom k) ha

/-- Actual inverse weights on the original finite-support decomposition. -/
def nativeEulerInverse : L →ₗ[k] L :=
  (DirectSum.toModule k ℕ L (fun i => (i : k)⁻¹ • (ℒ i).subtype)).comp
    (DirectSum.decomposeLinearEquiv ℒ).toLinearMap

/-- The inverse-weight operator's actual homogeneous action. -/
theorem nativeEulerInverse_homogeneous (i : ℕ) (a : ℒ i) :
    nativeEulerInverse k L ℒ a = (i : k)⁻¹ • (a : L) := by
  change (DirectSum.toModule k ℕ L (fun j => (j : k)⁻¹ • (ℒ j).subtype))
    (DirectSum.decomposeLinearEquiv ℒ (a : L)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rfl

/-- Positivity removes the only zero Euler weight. No inverse or
injectivity of the actual derivation is assumed. -/
theorem nativeEulerInverse_comp_euler (hzero : ℒ 0 = ⊥) :
    (nativeEulerInverse k L ℒ).comp (nativeEulerDerivation k L ℒ).toLinearMap =
      LinearMap.id := by
  apply DirectSum.decompose_lhom_ext ℒ
  intro i
  apply LinearMap.ext
  intro a
  change nativeEulerInverse k L ℒ (nativeEulerDerivation k L ℒ a) = (a : L)
  rw [nativeEulerDerivation_of_mem k L ℒ i a a.property,
    map_smul, nativeEulerInverse_homogeneous]
  by_cases hi : i = 0
  · subst i
    have ha : (a : L) = 0 := by
      simpa only [hzero, Submodule.mem_bot] using a.property
    simp only [ha, smul_zero]
  · rw [smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hi), one_smul]

/-- The actual positive Euler derivation is injective on the actual Lie algebra. -/
theorem nativeEulerDerivation_injective (hzero : ℒ 0 = ⊥) :
    Function.Injective (nativeEulerDerivation k L ℒ) := by
  have hleft : Function.LeftInverse (nativeEulerInverse k L ℒ)
      (nativeEulerDerivation k L ℒ) := by
    intro x
    exact congrArg (fun f : L →ₗ[k] L => f x)
      (nativeEulerInverse_comp_euler k L ℒ hzero)
  exact hleft.injective

/-- The already constructed genuine affine adjoint is consequently
faithful for the genuine positive Euler derivation. -/
theorem nativeEulerAffineAdjoint_injective (hzero : ℒ 0 = ⊥) :
    Function.Injective (derivationAffineAdjoint k L (nativeEulerDerivation k L ℒ)) :=
  derivationAffineAdjoint_injective k L (nativeEulerDerivation k L ℒ)
    (nativeEulerDerivation_injective k L ℒ hzero)

end ChenRanks.LieComparison
