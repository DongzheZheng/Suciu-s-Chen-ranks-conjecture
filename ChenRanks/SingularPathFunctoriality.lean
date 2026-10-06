import ChenRanks.SingularClosedPathEvaluation
import ChenRanks.SingularCocycleFunctoriality

/-!
# Native path cycles and their actual singular pullbacks

Every continuous map sends the original singular simplex of a genuine
path to the original simplex of its image. Evaluation of actual native
cohomology on these cycles therefore commutes with genuine pullback.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The genuine native simplex map has its original geometric meaning. -/
theorem geometricSimplex_simplexMap (f : C(X, Y)) (n : ℕ) (s : simplices X n)
    (x : stdSimplex ℝ (Fin (n + 1))) :
    geometricSimplex Y n (simplexMap f n s) x = f (geometricSimplex X n s x) := by
  rfl

/-- The same native one-simplex's genuine path is sent to its actual image. -/
theorem geometricSimplexPath_simplexMap (f : C(X, Y)) (s : simplices X 1) :
    geometricSimplexPath Y (simplexMap f 1 s) = f.comp (geometricSimplexPath X s) := by
  ext t
  exact geometricSimplex_simplexMap f 1 s (realSimplexIntervalMap t)

/-- Genuine unit-interval parametrization detects equality of original simplices. -/
theorem geometricSimplexPath_injective : Function.Injective (geometricSimplexPath X) := by
  intro s t h
  apply (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 1))).injective
  apply ContinuousMap.ext
  intro x
  have hx := DFunLike.congr_fun h (stdSimplexHomeomorphUnitInterval x)
  change geometricSimplex X 1 s
      (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval x)) =
    geometricSimplex X 1 t
      (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval x)) at hx
  simpa only [Homeomorph.symm_apply_apply] using hx

/-- The actual singular simplex of an image path is the native image simplex. -/
theorem simplexMap_simplexOfPath (f : C(X, Y)) (γ : C(I, X)) :
    simplexMap f 1 (simplexOfPath X γ) = simplexOfPath Y (f.comp γ) := by
  apply geometricSimplexPath_injective
  rw [geometricSimplexPath_simplexMap, geometricSimplexPath_simplexOfPath,
    geometricSimplexPath_simplexOfPath]

variable (k : Type) [Field k]

/-- Evaluation on native actual closed paths commutes with native cohomology pullback. -/
theorem closedPathEvaluation_cohomologyPullback (f : C(X, Y))
    (γ : C(I, X)) (hγ : γ 0 = γ 1) (a : cohomology k Y 1) :
    closedPathEvaluation k X γ hγ (cohomologyPullback k f 1 a) =
      closedPathEvaluation k Y (f.comp γ) (congrArg f hγ) a := by
  obtain ⟨b, rfl⟩ := cocycleClass_surjective k Y 1 a
  rw [cohomologyPullback_cocycleClass, closedPathEvaluation_cocycleClass,
    closedPathEvaluation_cocycleClass, cocycleCochain_cocyclePullback,
    values_cochainPullback, simplexMap_simplexOfPath]

end ChenRanks.SingularCohomology
