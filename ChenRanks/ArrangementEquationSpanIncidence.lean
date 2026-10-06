import ChenRanks.FiniteSimultaneousDualSeparation

/-!
# Actual affine points realizing original equation-span incidence

A subspace of the original polynomial space which does not contain the
constant one imposes consistent affine equation constraints. A true
quotient-dual functional simultaneously detects the finitely many
original equations outside that subspace. Normalizing its constant
value and taking its values on the original coordinate variables then
constructs an actual affine point with exactly the required original
equation incidence. Polynomial offsets are retained throughout.

This is an actual existence theorem, not an assumed generic-point or
intersection-lattice identification.
-/

noncomputable section
open scoped BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- A normalized genuine polynomial-space linear functional agrees
with actual affine evaluation on constants. -/
theorem normalizedPolynomialFunctional_C
    (f : CoordinateRing (d := d) →ₗ[ℂ] ℂ) (hf : f 1 = 1) (c : ℂ) :
    f (MvPolynomial.C c) = c := by
  have hc : (MvPolynomial.C c : CoordinateRing (d := d)) = c • 1 := by
    simp only [MvPolynomial.smul_eq_C_mul, mul_one]
  rw [hc, map_smul, hf, smul_eq_mul, mul_one]

/-- Its actual coordinate values recover evaluation on every original
affine equation; this does not assert multiplicativity on all polynomials. -/
theorem normalizedPolynomialFunctional_equation
    (f : CoordinateRing (d := d) →ₗ[ℂ] ℂ) (hf : f 1 = 1) (H : ι) :
    f (A.equationPolynomial H) =
      A.normal H (fun j => f (MvPolynomial.X j)) - A.offset H := by
  rw [equationPolynomial, map_sub, map_sum,
    normalizedPolynomialFunctional_C f hf (A.offset H),
    A.normal_eq_coordinate_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- An actual original affine point has precisely the original
hyperplanes whose affine equation polynomials belong to X.
In particular no generic point or expected incidence list is an input. -/
theorem exists_actual_point_with_equation_span_incidence
    (X : Submodule ℂ (CoordinateRing (d := d)))
    (hX : (1 : CoordinateRing (d := d)) ∉ X) :
    ∃ x : Fin d → ℂ, ∀ H : ι,
      A.normal H x = A.offset H ↔ A.equationPolynomial H ∈ X := by
  classical
  let J := {H : ι // A.equationPolynomial H ∉ X}
  let p : Option J → CoordinateRing (d := d) :=
    fun j => match j with
      | none => 1
      | some H => A.equationPolynomial H.val
  have hp : ∀ j, p j ∉ X := by
    intro j
    cases j with
    | none => exact hX
    | some H => exact H.property
  obtain ⟨g, hgX, hgp⟩ := exists_dual_vanishing_subspace_simultaneously_nonzero X p hp
  have hg1 : g 1 ≠ 0 := hgp none
  let f : CoordinateRing (d := d) →ₗ[ℂ] ℂ := (g 1)⁻¹ • g
  have hf1 : f 1 = 1 := by
    change (g 1)⁻¹ * g 1 = 1
    exact inv_mul_cancel₀ hg1
  let x : Fin d → ℂ := fun j => f (MvPolynomial.X j)
  refine ⟨x, ?_⟩
  intro H
  have heq : f (A.equationPolynomial H) = A.normal H x - A.offset H :=
    A.normalizedPolynomialFunctional_equation f hf1 H
  constructor
  · intro hHx
    by_contra hnot
    have hnonzero : f (A.equationPolynomial H) ≠ 0 := by
      change (g 1)⁻¹ * g (A.equationPolynomial H) ≠ 0
      exact mul_ne_zero (inv_ne_zero hg1) (hgp (some ⟨H, hnot⟩))
    exact hnonzero (heq.trans (sub_eq_zero.mpr hHx))
  · intro hmem
    have hzero : f (A.equationPolynomial H) = 0 := by
      change (g 1)⁻¹ * g (A.equationPolynomial H) = 0
      rw [hgX _ hmem, mul_zero]
    exact sub_eq_zero.mp (heq.symm.trans hzero)

end ChenRanks.AffineArrangement
