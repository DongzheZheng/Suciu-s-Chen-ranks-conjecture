import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

/-!
# Genuine edge avoidance from actual affine-line avoidance

The condition is an actual algebraic condition on the endpoint. Its
consequence is derived for every real segment parameter; no edge or
puncture detector is supplied as an input.
-/

noncomputable section

namespace ChenRanks

/-- Avoiding the actual line through a and q makes the entire genuine
line through a and b avoid q, provided the fixed endpoint is not q. -/
theorem realAffineEdge_ne_of_line_avoidance {V : Type*}
    [AddCommGroup V] [Module ℝ V] (a b q : V) (hqa : q ≠ a)
    (hb : b - a ∉ Submodule.span ℝ ({q - a} : Set V)) (t : ℝ) :
    a + t • (b - a) ≠ q := by
  intro h
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero] at h
    exact hqa h.symm
  · apply hb
    let S := Submodule.span ℝ ({q - a} : Set V)
    have hqaS : q - a ∈ S := Submodule.subset_span (by simp)
    have hdiff : t • (b - a) = q - a := by
      rw [← h]
      abel
    have htv : t • (b - a) ∈ S := hdiff.symm ▸ hqaS
    have hba := S.smul_mem t⁻¹ htv
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using hba

/-- The literal ordered barycentric edge has the same avoidance
consequence, including both endpoints. -/
theorem realWeightedEdge_ne_of_line_avoidance {V : Type*}
    [AddCommGroup V] [Module ℝ V] (a b q : V) (hqa : q ≠ a)
    (hb : b - a ∉ Submodule.span ℝ ({q - a} : Set V)) (t : ℝ) :
    (1 - t) • a + t • b ≠ q := by
  have heq : (1 - t) • a + t • b = a + t • (b - a) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  exact realAffineEdge_ne_of_line_avoidance a b q hqa hb t

end ChenRanks
