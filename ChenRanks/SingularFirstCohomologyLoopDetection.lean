import ChenRanks.SingularPathCocycleAdditivity
import ChenRanks.SingularClosedPathEvaluation
import Mathlib.Topology.Connected.PathConnected

/-!
# Detecting actual first singular cohomology by all actual closed paths

For a path-connected original space, a genuine closed cochain whose
values vanish on every genuine closed path has a genuine zero-cochain
primitive. The primitive is explicitly defined using paths from a
basepoint and the actual values equivalence for the native singular
chains. This proves the converse to coboundary evaluation vanishing;
it does not assert that any selected finite family of loops generates.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

/-- The original point of a native singular zero-simplex. -/
def zeroSimplexPoint (s : simplices X 0) : X :=
  geometricSimplex X 0 s (stdSimplex.vertex 0)

/-- Native face zero is the genuine final endpoint. -/
theorem zeroSimplexPoint_vertex_zero (s : simplices X 1) :
    zeroSimplexPoint X (vertex X 0 s) = geometricSimplexPath X s 1 := by
  change geometricSimplex X 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 s)
      (stdSimplex.vertex 0) = _
  rw [geometricSimplex_face]
  change geometricSimplex X 1 s
      (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) (stdSimplex.vertex 0)) = _
  rw [stdSimplex.map_vertex]
  change geometricSimplex X 1 s (stdSimplex.vertex 1) = _
  rw [← realSimplexIntervalMap_one]
  rfl

/-- Native face one is the genuine initial endpoint. -/
theorem zeroSimplexPoint_vertex_one (s : simplices X 1) :
    zeroSimplexPoint X (vertex X 1 s) = geometricSimplexPath X s 0 := by
  change geometricSimplex X 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 s)
      (stdSimplex.vertex 0) = _
  rw [geometricSimplex_face]
  change geometricSimplex X 1 s
      (stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) (stdSimplex.vertex 0)) = _
  rw [stdSimplex.map_vertex]
  change geometricSimplex X 1 s (stdSimplex.vertex 0) = _
  rw [← realSimplexIntervalMap_zero]
  rfl

variable (k : Type) [Field k]

/-- An actual primitive in the native original zero-cochain module,
constructed from actual paths and actual original cochain values. -/
def closedPathPrimitive [PathConnectedSpace X] (base : X) (a : cochains k X 1) :
    cochains k X 0 :=
  ofValues k X 0 (fun s => actualPathCochainValue k X a
    (PathConnectedSpace.somePath base (zeroSimplexPoint X s)))

/-- Vanishing on all actual loops gives the actual differential of the
constructed primitive, not an assumed coboundary representative. -/
theorem differential_closedPathPrimitive [PathConnectedSpace X]
    (base : X) (a : cochains k X 1) (ha : differential k X 1 a = 0)
    (hloops : ∀ γ : C(I, X), γ 0 = γ 1 →
      values k X 1 a (simplexOfPath X γ) = 0) :
    differential k X 0 (closedPathPrimitive X k base a) = a := by
  apply cochain_ext k X 1
  intro s
  change values k X 1
      (differential k X 0 (closedPathPrimitive X k base a)) s = values k X 1 a s
  rw [values_differential_zero]
  simp only [closedPathPrimitive, values_ofValues]
  change actualPathCochainValue k X a
      (PathConnectedSpace.somePath base (zeroSimplexPoint X (vertex X 0 s))) -
    actualPathCochainValue k X a
      (PathConnectedSpace.somePath base (zeroSimplexPoint X (vertex X 1 s))) =
        values k X 1 a s
  rw [zeroSimplexPoint_vertex_zero, zeroSimplexPoint_vertex_one]
  let γ := geometricSimplexPath X s
  let p : Path (γ 0) (γ 1) := ⟨γ, rfl, rfl⟩
  have hp := actualPathCochainValue_eq_endpoint_difference k X a ha hloops base p
  have hs : simplexOfPath X p.toContinuousMap = s :=
    simplexOfPath_geometricSimplexPath X s
  change values k X 1 a (simplexOfPath X p.toContinuousMap) = _ at hp
  rw [hs] at hp
  exact hp.symm

/-- For actual cocycle representatives, all actual loop evaluations
vanish precisely when the actual native cohomology class is zero. -/
theorem cocycleClass_eq_zero_iff_closed_path_values [PathConnectedSpace X]
    (a : cocycles k X 1) :
    cocycleClass k X 1 a = 0 ↔
      ∀ γ : C(I, X), γ 0 = γ 1 →
        values k X 1 (cocycleCochain k X 1 a) (simplexOfPath X γ) = 0 := by
  constructor
  · intro ha
    exact cocycleClass_eq_zero_values_closed_path X k a ha
  · intro hloops
    let base : X := Classical.choice (inferInstance : Nonempty X)
    apply (cocycleClass_eq_zero_iff k X 1 a).mpr
    apply (mem_positive_boundaries_iff k X 0 a).mpr
    exact ⟨closedPathPrimitive X k base (cocycleCochain k X 1 a),
      differential_closedPathPrimitive X k base (cocycleCochain k X 1 a)
        (cocycleCochain_closed k X 1 a) hloops⟩

/-- Actual H¹ is detected by evaluations on all actual closed paths.
No finite meridian-generation or cohomology-basis hypothesis occurs. -/
theorem firstCohomology_eq_zero_iff_closed_path_evaluations [PathConnectedSpace X]
    (h : cohomology k X 1) :
    h = 0 ↔ ∀ (γ : C(I, X)) (hγ : γ 0 = γ 1),
      closedPathEvaluation k X γ hγ h = 0 := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective k X 1 h
  rw [cocycleClass_eq_zero_iff_closed_path_values X k a]
  simp only [closedPathEvaluation_cocycleClass]

end ChenRanks.SingularCohomology
