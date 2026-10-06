import ChenRanks.LieDerivationNativeExtension
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Algebra.Rat

/-!
# Native finite exponentials on the actual derivation extension

The rational scalar action is restriction of the actual original field
scalar action. The native exponential of an actually nilpotent native
adjoint is a true Lie automorphism of the same actual extension. Its
coordinate endomorphism is the native finite exponential of the actual
affine adjoint, by native conjugation and native exponential naturality.

Nilpotence is an explicit intermediate structural condition here. It is
not inferred from an arbitrary derivation. An application to a positive
Euler grading must construct its actual finite truncation and prove that
condition. This file does not assume or prove that all positive unipotent
automorphisms are such exponentials, or any monodromy/formality theorem.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]

/-- The actual rational action on the same native extension. -/
instance nativeDerivationExtensionRatModule (D : LieDerivation k L L) :
    Module ℚ (NativeDerivationExtension k L D) :=
  Module.compHom (NativeDerivationExtension k L D) (algebraMap ℚ k)

/-- The same actual native extension is a rational Lie algebra, using
its original scalar multiplication rather than a supplied new bracket. -/
instance nativeDerivationExtensionRatLieAlgebra (D : LieDerivation k L L) :
    LieAlgebra ℚ (NativeDerivationExtension k L D) where
  __ := nativeDerivationExtensionRatModule k L D
  lie_smul r x y := by
    change ⁅x, (algebraMap ℚ k r) • y⁆ = (algebraMap ℚ k r) • ⁅x, y⁆
    exact lie_smul _ _ _

/-- Rational scalars on the same original scalar-first coordinates. -/
instance nativeDerivationCoordinatesRatModule : Module ℚ (k × L) :=
  Module.compHom (k × L) (algebraMap ℚ k)

/-- The actual restricted rational action commutes with the actual field
action, so it acts on the same native field-linear endomorphism ring. -/
instance nativeDerivationExtensionRatScalarComm (D : LieDerivation k L L) :
    SMulCommClass k ℚ (NativeDerivationExtension k L D) where
  smul_comm c r p := by
    change c • ((algebraMap ℚ k r) • p) = (algebraMap ℚ k r) • (c • p)
    exact smul_comm c (algebraMap ℚ k r) p

/-- The same compatibility on the true scalar-first coordinates. -/
instance nativeDerivationCoordinatesRatScalarComm : SMulCommClass k ℚ (k × L) where
  smul_comm c r p := by
    change c • ((algebraMap ℚ k r) • p) = (algebraMap ℚ k r) • (c • p)
    exact smul_comm c (algebraMap ℚ k r) p

/-- Native exponential gives a genuine Lie automorphism when the actual
native adjoint has been proved nilpotent. -/
def nativeDerivationExtensionExponential (D : LieDerivation k L L) (x : L)
    (hx : IsNilpotent (nativeDerivationExtensionAdjoint k L D x).toLinearMap) :
    NativeDerivationExtension k L D ≃ₗ⁅k⁆ NativeDerivationExtension k L D :=
  LieDerivation.exp (nativeDerivationExtensionAdjoint k L D x) hx

/-- The actual underlying map is the actual native finite exponential. -/
theorem nativeDerivationExtensionExponential_apply
    (D : LieDerivation k L L) (x : L)
    (hx : IsNilpotent (nativeDerivationExtensionAdjoint k L D x).toLinearMap)
    (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionExponential k L D x hx p =
      IsNilpotent.exp (nativeDerivationExtensionAdjoint k L D x).toLinearMap p :=
  LieDerivation.exp_map_apply (nativeDerivationExtensionAdjoint k L D x) hx p

/-- Native conjugation takes the actual nilpotent adjoint to the actual
nilpotent coordinate operator; no nilpotence of that operator is supplied. -/
theorem nativeDerivationExtensionAdjointCoordinateEnd_isNilpotent
    (D : LieDerivation k L L) (x : L)
    (hx : IsNilpotent (nativeDerivationExtensionAdjoint k L D x).toLinearMap) :
    IsNilpotent (nativeDerivationExtensionAdjointCoordinateEnd k L D x) :=
  hx.map (nativeDerivationExtensionCoordinates k L D).conjRingEquiv

/-- The true automorphism in original coordinates is exactly the native
finite exponential of the true original affine adjoint. -/
theorem nativeDerivationExtensionExponential_coordinates
    (D : LieDerivation k L L) (x : L)
    (hx : IsNilpotent (nativeDerivationExtensionAdjoint k L D x).toLinearMap)
    (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionCoordinates k L D
      (nativeDerivationExtensionExponential k L D x hx p) =
      IsNilpotent.exp (nativeDerivationExtensionAdjointCoordinateEnd k L D x)
        (nativeDerivationExtensionCoordinates k L D p) := by
  have h := hx.map_exp (nativeDerivationExtensionCoordinates k L D).conjRingEquiv
  have hp := congrArg (fun f : Module.End k (k × L) =>
    f (nativeDerivationExtensionCoordinates k L D p)) h
  change nativeDerivationExtensionCoordinates k L D
    (IsNilpotent.exp (nativeDerivationExtensionAdjoint k L D x).toLinearMap
      ((nativeDerivationExtensionCoordinates k L D).symm
        (nativeDerivationExtensionCoordinates k L D p))) = _ at hp
  rw [LinearEquiv.symm_apply_apply] at hp
  exact hp

end ChenRanks.LieComparison
