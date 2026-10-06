import ChenRanks.SingularPullbackComposition

/-! Identity and split injectivity of the original native singular
pullbacks. The statements are derived from the native singular functor
on genuine simplices and the actual cocycle quotient maps. -/
noncomputable section
open CategoryTheory
namespace ChenRanks.SingularCohomology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

@[simp] theorem simplexMap_id (n : ℕ) (s : simplices X n) :
    simplexMap (ContinuousMap.id X) n s = s := by
  change ((TopCat.toSSet.map (𝟙 (TopCat.of X))).app
    (Opposite.op (SimplexCategory.mk n))) s = s
  have h := TopCat.toSSet.map_id (TopCat.of X)
  exact congrArg (fun f => (f.app (Opposite.op (SimplexCategory.mk n))) s) h

variable (k : Type) [Field k]

@[simp] theorem cochainPullback_id_apply (n : ℕ) (a : cochains k X n) :
    cochainPullback k (ContinuousMap.id X) n a = a := by
  apply cochain_ext k X n
  intro s
  change values k X n (cochainPullback k (ContinuousMap.id X) n a) s =
    values k X n a s
  rw [values_cochainPullback, simplexMap_id]

@[simp] theorem cocyclePullback_id_apply (n : ℕ) (a : cocycles k X n) :
    cocyclePullback k (ContinuousMap.id X) n a = a := by
  apply Subtype.ext
  change cocycleCochain k X n (cocyclePullback k (ContinuousMap.id X) n a) =
    cocycleCochain k X n a
  rw [cocycleCochain_cocyclePullback, cochainPullback_id_apply]

@[simp] theorem cohomologyPullback_id_apply (n : ℕ) (a : cohomology k X n) :
    cohomologyPullback k (ContinuousMap.id X) n a = a := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective k X n a
  rw [cohomologyPullback_cocycleClass, cocyclePullback_id_apply]

/-- A genuine continuous section makes the actual original pullback
injective in every degree, without a product cohomology hypothesis. -/
theorem cohomologyPullback_injective_of_section
    (f : C(X, Y)) (s : C(Y, X)) (h : ∀ y, f (s y) = y) (n : ℕ) :
    Function.Injective (cohomologyPullback k f n) := by
  have he : f.comp s = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    exact h
  intro a b hab
  have hp := congrArg (cohomologyPullback k s n) hab
  rw [cohomologyPullback_comp_apply, cohomologyPullback_comp_apply,
    he, cohomologyPullback_id_apply, cohomologyPullback_id_apply] at hp
  exact hp

end ChenRanks.SingularCohomology
