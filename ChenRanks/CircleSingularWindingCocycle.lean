import ChenRanks.SingularSimplexGeometricMaps
import ChenRanks.CircleSimplexArgumentLift
import ChenRanks.CirclePathLiftIncrementFormula
import ChenRanks.SingularCupCocycles
import ChenRanks.SingularCocycleCochains

/-!
# A genuine integer winding cocycle on the original singular circle

Each native one-simplex is its actual circle path. The winding integer
comes from the native covering lift. Each actual singular triangle has
one actual real lift, so its three edge integers telescope. Casting those
integers gives a closed cochain over any coefficient field and an actual
native degree-one singular cohomology class. No triangle identity or
cohomology model is supplied as a hypothesis.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

/-- The true integer winding value on an original native circle one-simplex. -/
def circleWindingValue (s : simplices Circle 1) : ℤ :=
  circlePathIntegerIncrement (geometricSimplexPath Circle s)

/-- All three original singular edges arise from one real lift of their
original singular triangle, giving the actual integer cocycle relation. -/
theorem circleWindingValue_triangle (s : simplices Circle 2) :
    circleWindingValue (edge Circle 2 s) + circleWindingValue (edge Circle 0 s) =
      circleWindingValue (edge Circle 1 s) := by
  let F := circleSimplexArgumentLift 2 (geometricSimplex Circle 2 s)
  let θ : Fin 3 → C(I, ℝ) := fun i => F.comp (realTriangleFacePath i)
  have hθ (i : Fin 3) (t : I) :
      Circle.exp (θ i t) = geometricSimplexPath Circle (edge Circle i s) t := by
    rw [geometricSimplexPath_edge]
    exact circleSimplexArgumentLift_projects 2 (geometricSimplex Circle 2 s)
      (realTriangleFacePath i t)
  have h0 : θ 2 0 = θ 1 0 := by
    change F (realTriangleFacePath 2 0) = F (realTriangleFacePath 1 0)
    rw [realTriangleFacePath_zero, realTriangleFacePath_zero]
    rfl
  have h1 : θ 2 1 = θ 0 0 := by
    change F (realTriangleFacePath 2 1) = F (realTriangleFacePath 0 0)
    rw [realTriangleFacePath_one, realTriangleFacePath_zero]
    rfl
  have h2 : θ 0 1 = θ 1 1 := by
    change F (realTriangleFacePath 0 1) = F (realTriangleFacePath 1 1)
    rw [realTriangleFacePath_one, realTriangleFacePath_one]
    rfl
  exact circlePathIntegerIncrement_triangle_of_lifted_endpoints
    (geometricSimplexPath Circle (edge Circle 2 s))
    (geometricSimplexPath Circle (edge Circle 0 s))
    (geometricSimplexPath Circle (edge Circle 1 s))
    (θ 2) (θ 0) (θ 1) (hθ 2) (hθ 0) (hθ 1) h0 h1 h2

variable (k : Type) [Field k]

/-- The original linear cochain whose values are the true winding integers. -/
def circleWindingCochain : cochains k Circle 1 :=
  ofValues k Circle 1 (fun s => (circleWindingValue s : k))

theorem values_circleWindingCochain (s : simplices Circle 1) :
    values k Circle 1 (circleWindingCochain k) s = (circleWindingValue s : k) :=
  congrFun (values_ofValues k Circle 1 (fun s => (circleWindingValue s : k))) s

/-- The actual original winding cochain is closed, by its proved integer triangle relation. -/
theorem differential_circleWindingCochain_eq_zero :
    differential k Circle 1 (circleWindingCochain k) = 0 := by
  apply cochain_ext k Circle 2
  intro s
  change values k Circle 2 (differential k Circle 1 (circleWindingCochain k)) s = 0
  rw [values_differential_one, values_circleWindingCochain,
    values_circleWindingCochain, values_circleWindingCochain]
  have h := congrArg (fun z : ℤ => (z : k)) (circleWindingValue_triangle s)
  simp only [Int.cast_add] at h
  linear_combination h

/-- The winding cocycle in the native kernel of the original differential. -/
def circleWindingCocycle : cocycles k Circle 1 :=
  toCocycle k Circle 1 (circleWindingCochain k) (differential_circleWindingCochain_eq_zero k)

/-- The genuine winding class in the original singular cohomology. -/
def circleWindingClass : cohomology k Circle 1 :=
  cocycleClass k Circle 1 (circleWindingCocycle k)

end ChenRanks.SingularCohomology
