import ChenRanks.SingularSquareTriangleGeometry
import Mathlib.Tactic

/-! A zero actual barycentric coordinate puts the original point on
the corresponding actual native face. Thus actual bad points are
strictly interior whenever the true boundary avoids the actual bad set.
-/

noncomputable section

open unitInterval

namespace ChenRanks

theorem exists_realTriangleFacePath_of_coordinate_eq_zero
    (p : stdSimplex ℝ (Fin 3)) (i : Fin 3) (hi : p i = 0) :
    ∃ t : I, p = SingularCohomology.realTriangleFacePath i t := by
  let t : I := ⟨p (i.succAbove 1), p.property.1 _, stdSimplex.le_one p _⟩
  refine ⟨t, ?_⟩
  have hs := p.property.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change p 0 + (p 1 + p 2) = 1 at hs
  apply Subtype.ext
  funext j
  change p j = SingularCohomology.realTriangleFacePath i t j
  rw [SingularCohomology.realTriangleFacePath_coordinate]
  dsimp only [t]
  fin_cases i <;> fin_cases j <;> simp [Fin.succAbove] at hi ⊢ <;> linarith

/-- The interior condition needed for the actual sector construction
is derived from genuine boundary avoidance and genuine bad membership. -/
theorem realTrianglePoint_coordinates_positive_of_boundary_avoidance
    (B : Set (stdSimplex ℝ (Fin 3)))
    (hboundary : ∀ (i : Fin 3) (t : I),
      SingularCohomology.realTriangleFacePath i t ∉ B)
    (p : stdSimplex ℝ (Fin 3)) (hp : p ∈ B) :
    ∀ i : Fin 3, 0 < p i := by
  intro i
  by_contra h
  have hi : p i = 0 := le_antisymm (le_of_not_gt h) (p.property.1 i)
  obtain ⟨t, ht⟩ := exists_realTriangleFacePath_of_coordinate_eq_zero p i hi
  exact hboundary i t (ht ▸ hp)

end ChenRanks
