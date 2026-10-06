import ChenRanks.RealAffineTriangleEquation
import Mathlib.Analysis.Convex.StdSimplex

/-! Genuine finite zero sets on the actual real standard fan triangle.
The equal-edge equation is treated by its actual nonzero constant and
radial-line obstruction. The nonconstant edge equation is treated by
actual injectivity, rather than an assumed finite-zero property. -/

noncomputable section

namespace ChenRanks

/-- The two actual independent barycentric coordinates determine the
entire original standard triangle point. -/
theorem stdTriangle_center_target_coordinates_injective :
    Function.Injective (fun p : stdSimplex ℝ (Fin 3) => (p 2, p 0)) := by
  intro p q hpq
  have h₂ := congrArg Prod.fst hpq
  have h₀ := congrArg Prod.snd hpq
  have hp := p.property.2
  have hq := q.property.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hp hq
  change p 0 + (p 1 + p 2) = 1 at hp
  change q 0 + (q 1 + q 2) = 1 at hq
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h₀
  · change p 1 = q 1
    change p 0 = q 0 at h₀
    change p 2 = q 2 at h₂
    linarith
  · exact h₂

/-- Actual fan equation values in the original barycentric coordinates:
vertex order is center, source, target. -/
def realFanTriangleEquation (a b c : ℂ) (p : stdSimplex ℝ (Fin 3)) : ℂ :=
  p 0 • c + p 1 • a + p 2 • b

/-- Native barycentric weights give precisely the real affine equation
map at the actual center/target coordinates. -/
theorem realFanTriangleEquation_eq_affine (a b c : ℂ)
    (p : stdSimplex ℝ (Fin 3)) :
    realFanTriangleEquation a b c p = realAffineTriangleEquation a b c (p 2, p 0) := by
  have hs := p.property.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change p 0 + (p 1 + p 2) = 1 at hs
  have h₁ : p 1 = 1 - p 0 - p 2 := by linarith
  change (p 0 : ℂ) * c + (p 1 : ℂ) * a + (p 2 : ℂ) * b =
    a + (p 2 : ℂ) * (b - a) + (p 0 : ℂ) * (c - a)
  rw [h₁]
  push_cast
  ring

/-- A genuine nonconstant edge equation and genuinely transverse
center equation give an injective actual standard-triangle equation. -/
theorem realFanTriangleEquation_injective (a b c : ℂ) (hab : b ≠ a)
    (hc : c - a ∉ Submodule.span ℝ ({b - a} : Set ℂ)) :
    Function.Injective (realFanTriangleEquation a b c) := by
  intro p q h
  have heq : realAffineTriangleEquation a b c (p 2, p 0) =
      realAffineTriangleEquation a b c (q 2, q 0) := by
    rw [← realFanTriangleEquation_eq_affine, ← realFanTriangleEquation_eq_affine]
    exact h
  exact stdTriangle_center_target_coordinates_injective
    (realAffineTriangleEquation_injective a b c hab hc heq)

/-- The actual triangle zero set is finite in both the genuine
nonconstant and the genuine constant-edge cases. -/
theorem realFanTriangleEquation_zeroSet_finite (a b c : ℂ) (ha : a ≠ 0)
    (hedge : c - a ∉ Submodule.span ℝ ({b - a} : Set ℂ))
    (hradial : c ∉ Submodule.span ℝ ({a} : Set ℂ)) :
    Set.Finite {p : stdSimplex ℝ (Fin 3) | realFanTriangleEquation a b c p = 0} := by
  by_cases hab : b = a
  · subst b
    have hz : ∀ p : stdSimplex ℝ (Fin 3), realFanTriangleEquation a a c p ≠ 0 := by
      intro p
      have hs := p.property.2
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
      change p 0 + (p 1 + p 2) = 1 at hs
      exact realAffineTriangle_constant_edge_ne_zero a c ha hradial
        (p 0) (p 1) (p 2) (by linarith)
    have heq : {p : stdSimplex ℝ (Fin 3) | realFanTriangleEquation a a c p = 0} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hz p
    rw [heq]
    exact Set.finite_empty
  · have hinj := realFanTriangleEquation_injective a b c hab hedge
    exact (Set.finite_singleton (0 : ℂ)).preimage hinj.injOn

end ChenRanks
