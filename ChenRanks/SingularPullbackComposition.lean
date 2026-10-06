import ChenRanks.SingularCocycleFunctoriality

/-!
# Composition of the original singular pullbacks

The composition identities are derived from the native singular-simplex
functor and the actual inclusions of native cocycles. They concern the
same original cohomology quotients as the arrangement cup product.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem simplexMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ)
    (s : simplices X n) :
    simplexMap (g.comp f) n s = simplexMap g n (simplexMap f n s) := by
  change ((TopCat.toSSet.map (TopCat.ofHom f ≫ TopCat.ofHom g)).app
    (Opposite.op (SimplexCategory.mk n))) s = _
  rw [Functor.map_comp]
  rfl

variable (k : Type) [Field k]

theorem cochainPullback_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ)
    (a : cochains k Z n) :
    cochainPullback k f n (cochainPullback k g n a) =
      cochainPullback k (g.comp f) n a := by
  apply cochain_ext k X n
  intro s
  change values k X n (cochainPullback k f n (cochainPullback k g n a)) s =
    values k X n (cochainPullback k (g.comp f) n a) s
  rw [values_cochainPullback, values_cochainPullback,
    values_cochainPullback, simplexMap_comp]

theorem cocyclePullback_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ)
    (a : cocycles k Z n) :
    cocyclePullback k f n (cocyclePullback k g n a) =
      cocyclePullback k (g.comp f) n a := by
  apply Subtype.ext
  change cocycleCochain k X n (cocyclePullback k f n (cocyclePullback k g n a)) =
    cocycleCochain k X n (cocyclePullback k (g.comp f) n a)
  rw [cocycleCochain_cocyclePullback, cocycleCochain_cocyclePullback,
    cocycleCochain_cocyclePullback, cochainPullback_comp_apply]

theorem cohomologyPullback_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ)
    (a : cohomology k Z n) :
    cohomologyPullback k f n (cohomologyPullback k g n a) =
      cohomologyPullback k (g.comp f) n a := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective k Z n a
  rw [cohomologyPullback_cocycleClass, cohomologyPullback_cocycleClass,
    cohomologyPullback_cocycleClass, cocyclePullback_comp_apply]

end ChenRanks.SingularCohomology
