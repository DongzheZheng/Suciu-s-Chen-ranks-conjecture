import ChenRanks.NativeEulerExtensionRaisingFlag
import ChenRanks.ContinuousDegreeRaisingEndomorphisms
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Actual finite native Euler extension and its original continuous adjoint

The finite dimension of the native extension follows from its actual
coordinate equivalence with the original scalar field times the original
Lie algebra. The original finite coordinate norm then makes every original
linear operator continuous. Native adjoint functoriality and the genuine
endomorphism algebra equivalence construct the continuous Lie morphism.
Its value is proved to be the original extension derivation; positivity
of the actual grading proves faithfulness and the actual raising property.

No selected finite-dimensional model, norm, continuous representation,
faithfulness or raising-operator property is an input. The actual graded
Lie algebra is an intermediate original input; the arrangement's native
finite truncation supplies it by its separate proved factory.
-/

noncomputable section

namespace ChenRanks.LieComparison

section FiniteNativeExtension

variable (k L : Type*) [Field k] [LieRing L] [LieAlgebra k L]
variable [FiniteDimensional k L]

/-- The actual native extension is finite, by its genuine original
coordinate equivalence, rather than a chosen model-finiteness premise. -/
theorem nativeDerivationExtension_finiteDimensional (D : LieDerivation k L L) :
    FiniteDimensional k (NativeDerivationExtension k L D) :=
  Module.Finite.of_surjective
    (nativeDerivationExtensionCoordinates k L D).symm.toLinearMap
    (nativeDerivationExtensionCoordinates k L D).symm.surjective

end FiniteNativeExtension

section ContinuousNativeExtension

variable (k L : Type*) [NontriviallyNormedField k] [CompleteSpace k]
variable [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
variable (D : LieDerivation k L L)

local instance continuousNativeExtensionFiniteDimensional :
    FiniteDimensional k (NativeDerivationExtension k L D) :=
  nativeDerivationExtension_finiteDimensional k L D

/-- The genuine original finite coordinate norm on the genuine native extension. -/
abbrev nativeDerivationExtensionNormedAddCommGroup :
    NormedAddCommGroup (NativeDerivationExtension k L D) :=
  nativeFiniteNormedAddCommGroup k (NativeDerivationExtension k L D)

local instance continuousNativeExtensionNormedAddCommGroup :
    NormedAddCommGroup (NativeDerivationExtension k L D) :=
  nativeDerivationExtensionNormedAddCommGroup k L D

/-- The actual original scalar action for the genuine coordinate norm. -/
abbrev nativeDerivationExtensionNormedSpace :
    NormedSpace k (NativeDerivationExtension k L D) :=
  nativeFiniteNormedSpace k (NativeDerivationExtension k L D)

local instance continuousNativeExtensionNormedSpace :
    NormedSpace k (NativeDerivationExtension k L D) :=
  nativeDerivationExtensionNormedSpace k L D

/-- The original adjoint of the original native inclusion is a native
Lie morphism into original linear endomorphisms. -/
def nativeDerivationExtensionLinearAdjoint :
    L →ₗ⁅k⁆ Module.End k (NativeDerivationExtension k L D) :=
  (LieAlgebra.ad k (NativeDerivationExtension k L D)).comp
    (nativeDerivationExtensionOriginal k L D)

/-- The original native Lie morphism is the original extension derivation
at every original vector, with the native right-inner convention resolved. -/
theorem nativeDerivationExtensionLinearAdjoint_apply
    (x : L) (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionLinearAdjoint k L D x p =
      nativeDerivationExtensionAdjoint k L D x p := by
  change ⁅nativeDerivationExtensionOriginal k L D x, p⁆ =
    -⁅p, nativeDerivationExtensionOriginal k L D x⁆
  exact (lie_skew (nativeDerivationExtensionOriginal k L D x) p).symm

/-- Genuine continuity of the genuine original adjoint preserves the
actual associative commutator and therefore the actual Lie morphism. -/
def nativeDerivationExtensionContinuousAdjoint :
    L →ₗ⁅k⁆ ((NativeDerivationExtension k L D) →L[k]
      (NativeDerivationExtension k L D)) :=
  (nativeFiniteEndContinuousAlgEquiv k (NativeDerivationExtension k L D)).toLieEquiv.toLieHom.comp
    (nativeDerivationExtensionLinearAdjoint k L D)

@[simp] theorem nativeDerivationExtensionContinuousAdjoint_apply
    (x : L) (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionContinuousAdjoint k L D x p =
      nativeDerivationExtensionAdjoint k L D x p :=
  nativeDerivationExtensionLinearAdjoint_apply k L D x p

end ContinuousNativeExtension

section Euler

variable (k L : Type*) [NontriviallyNormedField k] [CompleteSpace k] [CharZero k]
variable [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]

local instance continuousEulerExtensionFiniteDimensional :
    FiniteDimensional k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) :=
  nativeDerivationExtension_finiteDimensional k L (nativeEulerDerivation k L ℒ)
local instance continuousEulerExtensionNormedAddCommGroup :
    NormedAddCommGroup (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) :=
  nativeDerivationExtensionNormedAddCommGroup k L (nativeEulerDerivation k L ℒ)
local instance continuousEulerExtensionNormedSpace :
    NormedSpace k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) :=
  nativeDerivationExtensionNormedSpace k L (nativeEulerDerivation k L ℒ)

/-- The actual native Euler adjoint is genuinely faithful, detected on
the actual distinguished axis and the proved injective Euler derivation. -/
theorem nativeEulerExtensionContinuousAdjoint_injective (hzero : ℒ 0 = ⊥) :
    Function.Injective
      (nativeDerivationExtensionContinuousAdjoint k L (nativeEulerDerivation k L ℒ)) := by
  intro x y hxy
  apply nativeEulerDerivation_injective k L ℒ hzero
  have h := congrArg (fun f =>
    (nativeDerivationExtensionCoordinates k L (nativeEulerDerivation k L ℒ)
      (f (nativeDerivationExtensionAxis k L (nativeEulerDerivation k L ℒ)))).2) hxy
  simp only [nativeDerivationExtensionContinuousAdjoint_apply,
    nativeDerivationExtensionAdjoint_coordinates] at h
  change (1 : k) • nativeEulerDerivation k L ℒ x + ⁅x, (0 : L)⁆ =
    (1 : k) • nativeEulerDerivation k L ℒ y + ⁅y, (0 : L)⁆ at h
  simpa only [one_smul, lie_zero, add_zero] using h

/-- The actual continuous Euler adjoint belongs to the actual constructed
degree-one continuous-operator subspace. This property is derived. -/
theorem nativeEulerExtensionContinuousAdjoint_mem_raising
    (hzero : ℒ 0 = ⊥) (x : L) :
    nativeDerivationExtensionContinuousAdjoint k L (nativeEulerDerivation k L ℒ) x ∈
      continuousDegreeRaisingEndomorphisms k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 1 := by
  apply (mem_continuousDegreeRaisingEndomorphisms k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (nativeEulerExtensionFlag k L ℒ) 1 _).mpr
  have he :
      (nativeDerivationExtensionContinuousAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap =
        (nativeDerivationExtensionAdjoint k L (nativeEulerDerivation k L ℒ) x).toLinearMap := by
    apply LinearMap.ext
    intro p
    exact nativeDerivationExtensionContinuousAdjoint_apply k L
      (nativeEulerDerivation k L ℒ) x p
  rw [he]
  exact nativeEulerExtensionAdjoint_mem_raisingEndomorphisms k L ℒ hzero x

end Euler

end ChenRanks.LieComparison
