import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-! The true one-equation limit models of a fan triangle. Independent
edge/center directions give an injective actual affine equation map.
A constant nonzero edge equation plus a noncollinear center equation
has no zero anywhere in the actual affine triangle. -/

noncomputable section

namespace ChenRanks

/-- A genuine two-vector dependence vanishes coefficientwise when the
second vector lies outside the true span of the nonzero first vector. -/
theorem real_two_term_coefficients_eq_zero {V : Type*} [AddCommGroup V]
    [Module ℝ V] (u v : V) (hu : u ≠ 0)
    (hv : v ∉ Submodule.span ℝ ({u} : Set V)) (s t : ℝ)
    (h : s • u + t • v = 0) : s = 0 ∧ t = 0 := by
  have ht : t = 0 := by
    by_contra ht
    apply hv
    let S := Submodule.span ℝ ({u} : Set V)
    have huS : u ∈ S := Submodule.subset_span (by simp)
    have hsum : s • u + t • v ∈ S := by
      rw [h]
      exact S.zero_mem
    have htv : t • v ∈ S := by
      have hsub := S.sub_mem hsum (S.smul_mem s huS)
      simpa only [add_sub_cancel_left] using hsub
    have hvS := S.smul_mem t⁻¹ htv
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using hvS
  refine ⟨?_, ht⟩
  rw [ht, zero_smul, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_right hu

/-- The literal affine equation-value map of a real triangle. -/
def realAffineTriangleEquation (a b c : ℂ) (p : ℝ × ℝ) : ℂ :=
  a + p.1 • (b - a) + p.2 • (c - a)

/-- The native affine equation map is injective when its actual center
avoids the original edge's actual real affine line. -/
theorem realAffineTriangleEquation_injective (a b c : ℂ) (hab : b ≠ a)
    (hc : c - a ∉ Submodule.span ℝ ({b - a} : Set ℂ)) :
    Function.Injective (realAffineTriangleEquation a b c) := by
  intro p q hpq
  have hzero : (p.1 - q.1) • (b - a) + (p.2 - q.2) • (c - a) = 0 := by
    change (((p.1 - q.1 : ℝ) : ℂ) * (b - a)) +
      (((p.2 - q.2 : ℝ) : ℂ) * (c - a)) = 0
    change a + (p.1 : ℂ) * (b - a) + (p.2 : ℂ) * (c - a) =
      a + (q.1 : ℂ) * (b - a) + (q.2 : ℂ) * (c - a) at hpq
    push_cast
    linear_combination hpq
  have hcoeff := real_two_term_coefficients_eq_zero (b - a) (c - a)
    (sub_ne_zero.mpr hab) hc (p.1 - q.1) (p.2 - q.2) hzero
  exact Prod.ext (sub_eq_zero.mp hcoeff.1) (sub_eq_zero.mp hcoeff.2)

/-- A constant nonzero edge equation has no zero on any actual affine
fan triangle whose center equation lies outside its true radial line.
This is the genuine constant-edge degeneration, not an injective map. -/
theorem realAffineTriangle_constant_edge_ne_zero (a c : ℂ) (ha : a ≠ 0)
    (hc : c ∉ Submodule.span ℝ ({a} : Set ℂ)) (r s t : ℝ)
    (hsum : r + s + t = 1) : r • c + s • a + t • a ≠ 0 := by
  intro hz
  have heq : (s + t) • a + r • c = 0 := by
    change (((s + t : ℝ) : ℂ) * a) + (r : ℂ) * c = 0
    change (r : ℂ) * c + (s : ℂ) * a + (t : ℂ) * a = 0 at hz
    push_cast
    linear_combination hz
  have hcoeff := real_two_term_coefficients_eq_zero a c ha hc (s + t) r heq
  linarith [hcoeff.1, hcoeff.2]

end ChenRanks
