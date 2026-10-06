import ChenRanks.SingularSimplexGeometricMaps
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Genuine triangular parametrizations of the original square

The two maps have actual vertex orders (00,10,11) and (00,01,11).
Their native real-simplex face parametrizations give the original square
edges with identical orientations. These geometric identities are used
later to construct a genuine periodic singular two-cycle.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

/-- The actual positive triangle parametrization, with its true interval bounds. -/
def realSquarePositiveTriangle : C(stdSimplex ℝ (Fin 3), I × I) where
  toFun x := (⟨x 1 + x 2, by
      constructor
      · exact add_nonneg (x.property.1 1) (x.property.1 2)
      · have hs := x.property.2
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
        change x 0 + (x 1 + x 2) = 1 at hs
        have hx : 0 ≤ x 0 := x.property.1 0
        linarith⟩,
    ⟨x 2, x.property.1 2, stdSimplex.le_one x 2⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_apply 1).comp continuous_subtype_val).add
        ((continuous_apply 2).comp continuous_subtype_val)
    · apply Continuous.subtype_mk
      exact (continuous_apply 2).comp continuous_subtype_val

/-- The second triangle is the actual coordinate-swapped first triangle. -/
def realSquareNegativeTriangle : C(stdSimplex ℝ (Fin 3), I × I) :=
  (⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩ : C(I × I, I × I)).comp
    realSquarePositiveTriangle

/-- Each actual native triangle face is computed in the true barycentric coordinates. -/
theorem realTriangleFacePath_coordinate (i : Fin 3) (t : I) (j : Fin 3) :
    realTriangleFacePath i t j =
      if j = i.succAbove 0 then 1 - (t : ℝ)
      else if j = i.succAbove 1 then (t : ℝ) else 0 := by
  change FunOnFinite.linearMap ℝ ℝ (fun k : Fin 2 => i.succAbove k)
    (stdSimplexHomeomorphUnitInterval.symm t) j = _
  rw [FunOnFinite.linearMap_apply_apply]
  change (Finset.univ.filter (fun k : Fin 2 => i.succAbove k = j)).sum
    (fun k => ![1 - (t : ℝ), (t : ℝ)] k) = _
  fin_cases i <;> fin_cases j <;>
    simp [Finset.sum_filter, Fin.sum_univ_succ, stdSimplexHomeomorphUnitInterval,
      stdSimplexEquivIcc, Fin.succAbove]


/-- The genuine positive triangle's boundary follows right, diagonal and bottom. -/
theorem realSquarePositiveTriangle_face (i : Fin 3) (t : I) :
    realSquarePositiveTriangle (realTriangleFacePath i t) =
      if i = 0 then (1, t) else if i = 1 then (t, t) else (t, 0) := by
  fin_cases i <;> apply Prod.ext <;> apply Subtype.ext <;>
    simp [realSquarePositiveTriangle, realTriangleFacePath_coordinate, Fin.succAbove]

/-- The genuine negative triangle's boundary follows top, diagonal and left. -/
theorem realSquareNegativeTriangle_face (i : Fin 3) (t : I) :
    realSquareNegativeTriangle (realTriangleFacePath i t) =
      if i = 0 then (t, 1) else if i = 1 then (t, t) else (0, t) := by
  rw [realSquareNegativeTriangle, ContinuousMap.comp_apply,
    realSquarePositiveTriangle_face]
  fin_cases i <;> simp

end ChenRanks.SingularCohomology
