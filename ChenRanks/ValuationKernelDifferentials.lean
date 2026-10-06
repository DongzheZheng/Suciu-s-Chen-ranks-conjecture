import ChenRanks.IntegerKernel
import ChenRanks.LogarithmicDifferentials
import ChenRanks.AlgebraicDifferentials

/-!
# From integral kernel products to actual relative logarithmic differentials

This module connects the integer-matrix theorem to actual Kähler
differentials. The remaining geometric input is explicit: every integral
kernel product must be algebraic over the curve field. This property is
not asserted or assumed for arrangements by a project axiom.

One way to prove that input is to use the manuscript's proper-fibre
argument. An alternative is to construct a relative divisor valuation
detecting every function transcendental over the curve field. Neither
construction is implemented here.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable {L F m n : Type*} [Field L] [CharZero L] [Field F]
  [Algebra ℂ L] [Algebra L F] [Algebra ℂ F] [IsScalarTower ℂ L F]
  [Fintype m] [Fintype n]

/-- Complex linear combinations of actual relative logarithmic forms. -/
def relativeLogCombination (u : n → Fˣ) : (n → ℂ) →ₗ[ℂ] Ω[F⁄L] where
  toFun c := ∑ j, c j • logarithmicDifferential L F (u j)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

omit [CharZero L] in
/-- Integral linear combinations are logarithmic differentials of the
actual products of integer powers, including negative powers. -/
theorem relativeLogCombination_integral (u : n → Fˣ) (z : n → ℤ) :
    relativeLogCombination (L := L) u (complexOfInt z) =
      logarithmicDifferential L F (∏ j, u j ^ z j) := by
  rw [logarithmicDifferential_prod_zpow]
  simp only [relativeLogCombination, LinearMap.coe_mk, AddHom.coe_mk,
    complexOfInt, Int.cast_smul_eq_zsmul]

/-- Conditional only on the stated algebraicity of the actual integral
kernel products. The complex kernel and logarithmic product identities
are conclusions of imported proofs, not additional assumptions. -/
theorem relativeLogCombination_eq_zero_of_kernel_products_algebraic
    (B : Matrix m n ℤ) (u : n → Fˣ)
    (hProducts : ∀ z : n → ℤ, B.mulVec z = 0 →
      IsAlgebraic L ((∏ j, u j ^ z j : Fˣ) : F))
    (β : n → ℂ) (hβ : (B.map (algebraMap ℤ ℂ)).mulVec β = 0) :
    relativeLogCombination (L := L) u β = 0 := by
  have hspan : Submodule.span ℂ (integerKernelVectors B) ≤
      LinearMap.ker (relativeLogCombination (L := L) u) := by
    apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [relativeLogCombination_integral]
    exact relative_logarithmic_differential_eq_zero_of_isAlgebraic
      ((∏ j, u j ^ z j : Fˣ) : F) (hProducts z hz)
  apply LinearMap.mem_ker.mp (hspan ?_)
  rw [← integer_matrix_complex_kernel_eq_span B]
  exact hβ

/-- The actual absolute logarithmic combination comes from the curve
field's differentials. This is the absolute form of the preceding kernel
theorem, obtained from the Kähler transitivity exact sequence. -/
theorem absoluteLogCombination_mem_baseChange_range_of_kernel_products_algebraic
    (B : Matrix m n ℤ) (u : n → Fˣ)
    (hProducts : ∀ z : n → ℤ, B.mulVec z = 0 →
      IsAlgebraic L ((∏ j, u j ^ z j : Fˣ) : F))
    (β : n → ℂ) (hβ : (B.map (algebraMap ℤ ℂ)).mulVec β = 0) :
    relativeLogCombination (L := ℂ) u β ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange ℂ L F) := by
  have hmap :
      (KaehlerDifferential.map ℂ L F F).restrictScalars ℂ
        (relativeLogCombination (L := ℂ) u β) =
      relativeLogCombination (L := L) u β := by
    simp only [relativeLogCombination, LinearMap.coe_mk, AddHom.coe_mk,
      map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    simp [logarithmicDifferential]
  apply (KaehlerDifferential.exact_mapBaseChange_map ℂ L F _).mp
  rw [← LinearMap.restrictScalars_apply ℂ, hmap]
  exact relativeLogCombination_eq_zero_of_kernel_products_algebraic B u hProducts β hβ

end ChenRanks
