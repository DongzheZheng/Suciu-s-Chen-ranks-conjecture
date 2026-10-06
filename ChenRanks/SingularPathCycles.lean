import ChenRanks.SingularSimplexGeometricMaps
import ChenRanks.SingularCupDifferentialIdentities
import ChenRanks.SingularCocycleCochains

/-!
# Original singular cycles from actual closed paths

An actual continuous path defines a native singular one-simplex using the
library's standard-simplex parametrization. Its true endpoints agree
when the path is closed. Thus its original singular boundary is zero,
and every actual degree-one coboundary evaluates to zero on it.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X]

/-- The native singular simplex of the original continuous path. -/
def simplexOfPath (γ : C(I, X)) : simplices X 1 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk 1))).symm
    (γ.comp ⟨stdSimplexHomeomorphUnitInterval,
      stdSimplexHomeomorphUnitInterval.continuous⟩)

/-- Its native geometric parametrization is exactly the given path. -/
theorem geometricSimplexPath_simplexOfPath (γ : C(I, X)) :
    geometricSimplexPath X (simplexOfPath X γ) = γ := by
  have h := (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 1))).apply_symm_apply
      (γ.comp ⟨stdSimplexHomeomorphUnitInterval,
        stdSimplexHomeomorphUnitInterval.continuous⟩)
  change geometricSimplex X 1 (simplexOfPath X γ) = _ at h
  ext t
  change geometricSimplex X 1 (simplexOfPath X γ)
    (stdSimplexHomeomorphUnitInterval.symm t) = γ t
  rw [h]
  exact congrArg γ (Homeomorph.apply_symm_apply stdSimplexHomeomorphUnitInterval t)

/-- The actual native endpoint simplices agree for a genuinely closed path. -/
theorem vertex_simplexOfPath_eq (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    vertex X 0 (simplexOfPath X γ) = vertex X 1 (simplexOfPath X γ) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 0))).injective
  apply ContinuousMap.ext
  intro x
  change geometricSimplex X 0 (vertex X 0 (simplexOfPath X γ)) x =
    geometricSimplex X 0 (vertex X 1 (simplexOfPath X γ)) x
  simp only [vertex]
  rw [geometricSimplex_face, geometricSimplex_face]
  have hx : x = (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 1)) := Subsingleton.elim _ _
  rw [hx]
  change geometricSimplex X 1 (simplexOfPath X γ)
      (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) (stdSimplex.vertex 0)) =
    geometricSimplex X 1 (simplexOfPath X γ)
      (stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) (stdSimplex.vertex 0))
  rw [stdSimplex.map_vertex, stdSimplex.map_vertex]
  have hp := geometricSimplexPath_simplexOfPath X γ
  have he0 := DFunLike.congr_fun hp 0
  have he1 := DFunLike.congr_fun hp 1
  change geometricSimplex X 1 (simplexOfPath X γ) (realSimplexIntervalMap 0) = γ 0 at he0
  change geometricSimplex X 1 (simplexOfPath X γ) (realSimplexIntervalMap 1) = γ 1 at he1
  rw [realSimplexIntervalMap_zero] at he0
  rw [realSimplexIntervalMap_one] at he1
  exact he1.trans (hγ.symm.trans he0.symm)

variable (k : Type) [Field k]

/-- The original singular boundary of an actual closed path is zero. -/
theorem boundary_simplexOfPath_eq_zero (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    ((chains k X).d 1 0).hom (simplexChain k X 1 (simplexOfPath X γ)) = 0 := by
  rw [boundary_simplexChain]
  simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_succ, Fin.val_zero, zero_add, pow_one, neg_one_zsmul,
    Fin.sum_univ_zero, add_zero]
  change simplexChain k X 0 (vertex X 0 (simplexOfPath X γ)) +
    -simplexChain k X 0 (vertex X 1 (simplexOfPath X γ)) = 0
  rw [vertex_simplexOfPath_eq X γ hγ, add_neg_cancel]

/-- Actual boundaries vanish on an actual closed path in the original chain module. -/
theorem values_boundary_on_closed_path (b : cochains k X 0)
    (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    values k X 1 (differential k X 0 b) (simplexOfPath X γ) = 0 := by
  rw [values_differential_zero, vertex_simplexOfPath_eq X γ hγ, sub_self]

/-- A vanishing actual cohomology class evaluates to zero on every genuine loop. -/
theorem cocycleClass_eq_zero_values_closed_path (a : cocycles k X 1)
    (ha : cocycleClass k X 1 a = 0) (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    values k X 1 (cocycleCochain k X 1 a) (simplexOfPath X γ) = 0 := by
  obtain ⟨b, hb⟩ := (mem_positive_boundaries_iff k X 0 a).mp
    ((cocycleClass_eq_zero_iff k X 1 a).mp ha)
  rw [← hb]
  exact values_boundary_on_closed_path X k b γ hγ

end ChenRanks.SingularCohomology
