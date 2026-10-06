import ChenRanks.ArrangementMeridianCircle
import ChenRanks.SingularPathFunctoriality
import ChenRanks.SingularSquareTriangleGeometry
import ChenRanks.SingularCupCocycles
import Mathlib.Tactic

/-!
# Genuine circle paths obtained from actual straight real arguments

The true exponential covering map sends each straight real interval to
an actual circle path. Actual affine real triangles give its native
singular cocycle addition law. Simultaneous actual period translation
leaves the original continuous circle path literally unchanged. These
identities are derived, not assigned as path-integration axioms.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

def circleStraightPath (a b : ℝ) : C(I, Circle) :=
  Circle.exp.comp ⟨fun t => (1 - (t : ℝ)) * a + (t : ℝ) * b, by fun_prop⟩

@[simp] theorem circleStraightPath_zero (a b : ℝ) :
    circleStraightPath a b 0 = Circle.exp a := by
  simp [circleStraightPath]

@[simp] theorem circleStraightPath_one (a b : ℝ) :
    circleStraightPath a b 1 = Circle.exp b := by
  simp [circleStraightPath]

theorem circleStraightPath_periodic (a b : ℝ) (n : ℤ) :
    circleStraightPath (a + (n : ℝ) * (2 * Real.pi))
      (b + (n : ℝ) * (2 * Real.pi)) = circleStraightPath a b := by
  apply ContinuousMap.ext
  intro t
  change Circle.exp ((1 - (t : ℝ)) * (a + (n : ℝ) * (2 * Real.pi)) +
      (t : ℝ) * (b + (n : ℝ) * (2 * Real.pi))) =
    Circle.exp ((1 - (t : ℝ)) * a + (t : ℝ) * b)
  rw [show (1 - (t : ℝ)) * (a + (n : ℝ) * (2 * Real.pi)) +
      (t : ℝ) * (b + (n : ℝ) * (2 * Real.pi)) =
      ((1 - (t : ℝ)) * a + (t : ℝ) * b) +
        (n : ℝ) * (2 * Real.pi) from by ring]
  rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

theorem circleStraightPath_positive_generator :
    circleStraightPath 0 (2 * Real.pi) = positiveUnitCircleTraversal := by
  apply ContinuousMap.ext
  intro t
  change Circle.exp ((1 - (t : ℝ)) * 0 + (t : ℝ) * (2 * Real.pi)) =
    Circle.exp ((2 * Real.pi) * (t : ℝ))
  congr 1
  ring

def circleStraightTriangleMap (a b c : ℝ) :
    C(stdSimplex ℝ (Fin 3), Circle) :=
  Circle.exp.comp ⟨fun p => p 0 * a + p 1 * b + p 2 * c, by
    have hc (i : Fin 3) : Continuous (fun p : stdSimplex ℝ (Fin 3) => p i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (((hc 0).mul continuous_const).add
      ((hc 1).mul continuous_const)).add ((hc 2).mul continuous_const)⟩

theorem circleStraightTriangleMap_face (a b c : ℝ) (i : Fin 3) :
    (circleStraightTriangleMap a b c).comp (realTriangleFacePath i) =
      if i = 0 then circleStraightPath b c
      else if i = 1 then circleStraightPath a c else circleStraightPath a b := by
  fin_cases i <;> apply ContinuousMap.ext <;> intro t
  all_goals
    simp [circleStraightTriangleMap, circleStraightPath,
      realTriangleFacePath_coordinate, Fin.succAbove]

def circleStraightTriangle (a b c : ℝ) : simplices Circle 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle)
    (Opposite.op (SimplexCategory.mk 2))).symm (circleStraightTriangleMap a b c)

theorem geometricSimplex_circleStraightTriangle (a b c : ℝ) :
    geometricSimplex Circle 2 (circleStraightTriangle a b c) =
      circleStraightTriangleMap a b c :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle)
    (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply _

theorem edge_circleStraightTriangle (a b c : ℝ) (i : Fin 3) :
    edge Circle i (circleStraightTriangle a b c) =
      if i = 0 then simplexOfPath Circle (circleStraightPath b c)
      else if i = 1 then simplexOfPath Circle (circleStraightPath a c)
      else simplexOfPath Circle (circleStraightPath a b) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_edge, geometricSimplex_circleStraightTriangle,
    circleStraightTriangleMap_face]
  fin_cases i <;> simp [geometricSimplexPath_simplexOfPath]

variable (k : Type) [Field k]

def circleStraightPathValue (β : cochains k Circle 1) (a b : ℝ) : k :=
  values k Circle 1 β (simplexOfPath Circle (circleStraightPath a b))

/-- The actual native affine triangle proves the genuine cocycle
addition law along actual straight argument paths. -/
theorem circleStraightPathValue_add (β : cochains k Circle 1)
    (hβ : differential k Circle 1 β = 0) (a b c : ℝ) :
    circleStraightPathValue k β a c =
      circleStraightPathValue k β a b + circleStraightPathValue k β b c := by
  have h := closedOne_triangle_relation k Circle β hβ (circleStraightTriangle a b c)
  simpa only [edge_circleStraightTriangle, circleStraightPathValue, ite_true,
    show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_false] using h

theorem circleStraightPathValue_self_eq_zero (β : cochains k Circle 1)
    (hβ : differential k Circle 1 β = 0) (a : ℝ) :
    circleStraightPathValue k β a a = 0 := by
  have h := circleStraightPathValue_add k β hβ a a a
  linear_combination -h

theorem circleStraightPathValue_periodic (β : cochains k Circle 1)
    (a b : ℝ) (n : ℤ) :
    circleStraightPathValue k β (a + (n : ℝ) * (2 * Real.pi))
      (b + (n : ℝ) * (2 * Real.pi)) = circleStraightPathValue k β a b := by
  unfold circleStraightPathValue
  rw [circleStraightPath_periodic]

end ChenRanks.SingularCohomology
