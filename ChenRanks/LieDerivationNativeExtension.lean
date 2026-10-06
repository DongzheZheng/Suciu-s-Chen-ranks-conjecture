import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# A genuine native semidirect extension for an actual Lie derivation

An actual derivation D defines the actual one-dimensional action a ↦ -aD.
The native semidirect-sum construction supplies its Lie ring and Lie algebra.
Its distinguished axis has adjoint -D on the original Lie algebra. The
actual adjoint of an original vector is itself an actual native derivation;
in the original coordinates it is the affine operator (a,y) ↦ (0,aDx+[x,y]).

The derivation here is arbitrary. An actual positive grading, an Euler
choice of D, nilpotence of the actual adjoints, and identification of all
positive unipotent automorphisms still require separate proofs. None of
those conclusions, an automorphism bijection, BCH, monodromy, or formality
is an input or conclusion of this construction.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L]

/-- The actual scalar action by the negative of the original derivation. -/
def nativeDerivationScalarAction (D : LieDerivation k L L) :
    k →ₗ⁅k⁆ LieDerivation k L L where
  toFun a := -(a • D)
  map_add' a b := by simp only [add_smul, neg_add]
  map_smul' a b := by
    change -((a * b) • D) = a • -(b • D)
    rw [smul_neg, smul_smul]
  map_lie' := by
    intro a b
    have hab : ⁅a, b⁆ = (0 : k) := by simp [Ring.lie_def, mul_comm]
    rw [hab]
    apply LieDerivation.ext
    intro z
    simp

/-- The actual native extension, retaining its native Lie bracket. -/
abbrev NativeDerivationExtension (D : LieDerivation k L L) :=
  LieAlgebra.SemiDirectSum L k (nativeDerivationScalarAction k L D)

/-- Original scalar-first coordinates, as a genuine linear equivalence. -/
def nativeDerivationExtensionCoordinates (D : LieDerivation k L L) :
    NativeDerivationExtension k L D ≃ₗ[k] k × L where
  toFun p := (p.right, p.left)
  invFun p := ⟨p.2, p.1⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  map_add' p q := rfl
  map_smul' a p := rfl

/-- The actual distinguished one-dimensional axis. -/
def nativeDerivationExtensionAxis (D : LieDerivation k L L) :
    NativeDerivationExtension k L D := ⟨0, 1⟩

/-- The actual original-vector inclusion into the native extension. -/
def nativeDerivationExtensionOriginal (D : LieDerivation k L L) :
    L →ₗ⁅k⁆ NativeDerivationExtension k L D :=
  LieAlgebra.SemiDirectSum.inl (nativeDerivationScalarAction k L D)

/-- The native adjoint is a genuine derivation of the genuine extension.
The native inner convention is the right adjoint, hence the negative. -/
def nativeDerivationExtensionAdjoint (D : LieDerivation k L L) (x : L) :
    LieDerivation k (NativeDerivationExtension k L D) (NativeDerivationExtension k L D) :=
  -LieDerivation.inner k (NativeDerivationExtension k L D)
    (NativeDerivationExtension k L D) (nativeDerivationExtensionOriginal k L D x)

/-- Exact original coordinates of that native derivation. -/
theorem nativeDerivationExtensionAdjoint_coordinates
    (D : LieDerivation k L L) (x : L) (p : NativeDerivationExtension k L D) :
    nativeDerivationExtensionCoordinates k L D
      (nativeDerivationExtensionAdjoint k L D x p) =
      (0, p.right • D x + ⁅x, p.left⁆) := by
  apply Prod.ext
  · change -⁅p.right, (0 : k)⁆ = 0
    simp only [lie_zero, neg_zero]
  · change -(⁅p.left, x⁆ + (-(p.right • D)) x - (-(0 • D)) p.left) = _
    simp only [LieDerivation.neg_apply, LieDerivation.smul_apply,
      zero_smul, neg_zero, LieDerivation.zero_apply, sub_zero]
    rw [← lie_skew p.left x]
    abel

/-- The actual axis action on every original vector is the negative
of the original derivation, with no grading property assumed. -/
theorem nativeDerivationExtensionAxis_bracket_original
    (D : LieDerivation k L L) (x : L) :
    nativeDerivationExtensionCoordinates k L D
      ⁅nativeDerivationExtensionAxis k L D, nativeDerivationExtensionOriginal k L D x⁆ =
      (0, -D x) := by
  apply Prod.ext
  · change ⁅(1 : k), 0⁆ = 0
    exact lie_zero _
  · change ⁅(0 : L), x⁆ + (-(1 • D)) x - (-(0 • D)) 0 = -D x
    simp only [zero_lie, one_smul, zero_smul, neg_zero,
      LieDerivation.neg_apply, LieDerivation.zero_apply, sub_zero, zero_add]

/-- The true native endomorphism expressed in the true original coordinates. -/
def nativeDerivationExtensionAdjointCoordinateEnd (D : LieDerivation k L L) (x : L) :
    Module.End k (k × L) :=
  (nativeDerivationExtensionCoordinates k L D).conjRingEquiv
    (nativeDerivationExtensionAdjoint k L D x).toLinearMap

/-- The native coordinate endomorphism is the original affine adjoint
formula, rather than a supplied affine representation. -/
theorem nativeDerivationExtensionAdjointCoordinateEnd_apply
    (D : LieDerivation k L L) (x : L) (p : k × L) :
    nativeDerivationExtensionAdjointCoordinateEnd k L D x p =
      (0, p.1 • D x + ⁅x, p.2⁆) := by
  change nativeDerivationExtensionCoordinates k L D
    (nativeDerivationExtensionAdjoint k L D x ⟨p.2, p.1⟩) = _
  exact nativeDerivationExtensionAdjoint_coordinates k L D x _

end ChenRanks.LieComparison
