import ChenRanks.CirclePathProductCarry
import ChenRanks.CircleSingularWindingCocycle
import ChenRanks.SingularPathFunctoriality

/-!
# Products of circle maps in actual singular first cohomology

The principal-argument carry is an actual zero-cochain. Its differential
is the discrepancy between the original winding cochains of a product
and its two factors. Thus the product identity holds in the native
singular cohomology quotient, without a cohomology-model identification.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable {X : Type} [TopologicalSpace X]

/-- The actual point represented by a native singular zero-simplex. -/
def geometricSimplexPoint (s : simplices X 0) : X :=
  geometricSimplex X 0 s (stdSimplex.vertex 0)

theorem geometricSimplexPoint_vertex_zero (s : simplices X 1) :
    geometricSimplexPoint (vertex X 0 s) = geometricSimplexPath X s 1 := by
  change geometricSimplex X 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 s)
    (stdSimplex.vertex 0) = geometricSimplex X 1 s (realSimplexIntervalMap 1)
  rw [geometricSimplex_face, realSimplexIntervalMap_one]
  change geometricSimplex X 1 s
    (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) (stdSimplex.vertex 0)) = _
  rw [stdSimplex.map_vertex]
  rfl

theorem geometricSimplexPoint_vertex_one (s : simplices X 1) :
    geometricSimplexPoint (vertex X 1 s) = geometricSimplexPath X s 0 := by
  change geometricSimplex X 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 s)
    (stdSimplex.vertex 0) = geometricSimplex X 1 s (realSimplexIntervalMap 0)
  rw [geometricSimplex_face, realSimplexIntervalMap_zero]
  change geometricSimplex X 1 s
    (stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) (stdSimplex.vertex 0)) = _
  rw [stdSimplex.map_vertex]
  rfl

variable (k : Type) [Field k]

/-- The genuine carry zero-cochain of the two actual circle maps. -/
def circleMapProductCarryCochain (f g : C(X, Circle)) : cochains k X 0 :=
  ofValues k X 0 (fun s =>
    (circleProductArgumentCarry (f (geometricSimplexPoint s))
      (g (geometricSimplexPoint s)) : k))

theorem values_circleMapProductCarryCochain (f g : C(X, Circle))
    (s : simplices X 0) :
    values k X 0 (circleMapProductCarryCochain k f g) s =
      (circleProductArgumentCarry (f (geometricSimplexPoint s))
        (g (geometricSimplexPoint s)) : k) :=
  congrFun (values_ofValues k X 0 _) s

/-- The actual native differential is the open-path argument correction. -/
theorem differential_circleMapProductCarryCochain (f g : C(X, Circle)) :
    differential k X 0 (circleMapProductCarryCochain k f g) =
      cochainPullback k (f * g) 1 (circleWindingCochain k) -
        cochainPullback k f 1 (circleWindingCochain k) -
        cochainPullback k g 1 (circleWindingCochain k) := by
  apply cochain_ext k X 1
  intro s
  change values k X 1
      (differential k X 0 (circleMapProductCarryCochain k f g)) s =
    values k X 1
      (cochainPullback k (f * g) 1 (circleWindingCochain k) -
        cochainPullback k f 1 (circleWindingCochain k) -
        cochainPullback k g 1 (circleWindingCochain k)) s
  rw [values_differential_zero, values_circleMapProductCarryCochain,
    values_circleMapProductCarryCochain, geometricSimplexPoint_vertex_zero,
    geometricSimplexPoint_vertex_one]
  simp only [map_sub, Pi.sub_apply, values_cochainPullback,
    values_circleWindingCochain, circleWindingValue, geometricSimplexPath_simplexMap]
  let γ := geometricSimplexPath X s
  have hmaps : (f * g).comp γ = (f.comp γ) * (g.comp γ) := by
    ext t
    rfl
  rw [hmaps]
  have h := congrArg (fun n : ℤ => (n : k))
    (circlePathIntegerIncrement_mul (f.comp γ) (g.comp γ))
  simp only [Int.cast_add, Int.cast_sub, ContinuousMap.comp_apply] at h
  change (circleProductArgumentCarry (f (γ 1)) (g (γ 1)) : k) -
    (circleProductArgumentCarry (f (γ 0)) (g (γ 0)) : k) = _
  linear_combination -h

/-- The product identity in the original native singular cohomology. -/
theorem cohomologyPullback_circleWindingClass_mul (f g : C(X, Circle)) :
    cohomologyPullback k (f * g) 1 (circleWindingClass k) =
      cohomologyPullback k f 1 (circleWindingClass k) +
        cohomologyPullback k g 1 (circleWindingClass k) := by
  let a : cocycles k X 1 :=
    cocyclePullback k (f * g) 1 (circleWindingCocycle k) -
      cocyclePullback k f 1 (circleWindingCocycle k) -
      cocyclePullback k g 1 (circleWindingCocycle k)
  have ha : a ∈ boundaries k X 1 := by
    apply (mem_positive_boundaries_iff k X 0 a).mpr
    refine ⟨circleMapProductCarryCochain k f g, ?_⟩
    rw [differential_circleMapProductCarryCochain]
    simp only [a, map_sub, cocycleCochain_cocyclePullback,
      circleWindingCocycle, cocycleCochain_toCocycle]
  have hz := (cocycleClass_eq_zero_iff k X 1 a).mpr ha
  simp only [a, map_sub] at hz
  rw [sub_sub] at hz
  have he := sub_eq_zero.mp hz
  simpa only [circleWindingClass, cohomologyPullback_cocycleClass] using he

/-- A constant circle map has zero original winding class. -/
theorem cohomologyPullback_circleWindingClass_const (z : Circle) :
    cohomologyPullback k (ContinuousMap.const X z) 1 (circleWindingClass k) = 0 := by
  have hzero : cochainPullback k (ContinuousMap.const X z) 1
      (circleWindingCochain k) = 0 := by
    apply cochain_ext k X 1
    intro s
    change values k X 1
      (cochainPullback k (ContinuousMap.const X z) 1 (circleWindingCochain k)) s = 0
    simp only [values_cochainPullback, values_circleWindingCochain,
      circleWindingValue, geometricSimplexPath_simplexMap, map_zero, Pi.zero_apply]
    have hpath : (ContinuousMap.const X z).comp (geometricSimplexPath X s) =
        ContinuousMap.const I z := by
      ext t
      rfl
    rw [hpath, circlePathIntegerIncrement_const, Int.cast_zero]
  rw [circleWindingClass, cohomologyPullback_cocycleClass]
  apply (cocycleClass_eq_zero_iff k X 1 _).mpr
  apply (mem_positive_boundaries_iff k X 0 _).mpr
  refine ⟨0, ?_⟩
  rw [cocycleCochain_cocyclePullback, circleWindingCocycle,
    cocycleCochain_toCocycle, hzero, map_zero]

/-- Taking the actual inverse circle map negates its native winding class. -/
theorem cohomologyPullback_circleWindingClass_inv (f : C(X, Circle)) :
    cohomologyPullback k f⁻¹ 1 (circleWindingClass k) =
      -(cohomologyPullback k f 1 (circleWindingClass k)) := by
  have h := cohomologyPullback_circleWindingClass_mul k f f⁻¹
  have hmaps : f * f⁻¹ = ContinuousMap.const X 1 := by
    ext x
    simp
  rw [hmaps, cohomologyPullback_circleWindingClass_const] at h
  calc
    cohomologyPullback k f⁻¹ 1 (circleWindingClass k) =
        -(cohomologyPullback k f 1 (circleWindingClass k)) +
          (cohomologyPullback k f 1 (circleWindingClass k) +
            cohomologyPullback k f⁻¹ 1 (circleWindingClass k)) := by abel
    _ = -(cohomologyPullback k f 1 (circleWindingClass k)) := by
      rw [← h, add_zero]

end ChenRanks.SingularCohomology
