import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Complex.Basic

/-!
# Actual real and imaginary coordinates of complex affine space

The coordinate equivalence is constructed from the real and imaginary
parts of the original complex coordinates.  Its inverse reconstructs each
complex coordinate from those same two real values.  Thus the finite real
basis used by coordinate differentiation is not supplied as geometric data.
The empty ambient dimension is included without a nonempty-coordinate
assumption.
-/

noncomputable section

namespace ChenRanks

/-- The true real coordinates of the original complex affine space. -/
def complexAffineRealCoordinates (d : ℕ) :
    (Fin d → ℂ) ≃ₗ[ℝ] ((Fin d × Fin 2) → ℝ) where
  toFun x i := if i.2 = 0 then (x i.1).re else (x i.1).im
  invFun c i := (c (i, 0) : ℂ) + c (i, 1) • Complex.I
  left_inv x := by
    funext i
    simp only [ite_true, ite_false]
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    exact Complex.re_add_im (x i)
  right_inv c := by
    funext i
    rcases i with ⟨j, a⟩
    fin_cases a <;> simp [RCLike.real_smul_eq_coe_mul (K := ℂ)]
  map_add' x y := by
    funext i
    rcases i with ⟨j, a⟩
    fin_cases a <;> simp
  map_smul' r x := by
    funext i
    rcases i with ⟨j, a⟩
    fin_cases a
    · change (r • x j).re = r * (x j).re
      exact RCLike.smul_re (K := ℂ) r (x j)
    · change (r • x j).im = r * (x j).im
      exact RCLike.smul_im (K := ℂ) r (x j)

@[simp] theorem complexAffineRealCoordinates_re
    (d : ℕ) (x : Fin d → ℂ) (i : Fin d) :
    complexAffineRealCoordinates d x (i, 0) = (x i).re := rfl

@[simp] theorem complexAffineRealCoordinates_im
    (d : ℕ) (x : Fin d → ℂ) (i : Fin d) :
    complexAffineRealCoordinates d x (i, 1) = (x i).im := rfl

/-- The actual finite real basis, transported from literal coordinate
functions through the proved real/imaginary coordinate equivalence. -/
def complexAffineRealBasis (d : ℕ) : Module.Basis (Fin d × Fin 2) ℝ (Fin d → ℂ) :=
  (Pi.basisFun ℝ (Fin d × Fin 2)).map (complexAffineRealCoordinates d).symm

/-- Its cardinality is the real dimension of the actual original ambient
space, including dimension zero. -/
theorem complexAffineRealBasis_finrank (d : ℕ) :
    Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_eq_card_basis (complexAffineRealBasis d)]
  simp [Fintype.card_prod, Nat.mul_comm]

end ChenRanks
