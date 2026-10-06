import ChenRanks.SingularCohomologyFunctoriality
import ChenRanks.SingularCupOne

/-!
# Functoriality on the original singular simplices

The chain map is the library's singular-chain functor, rather than an
independently chosen map on simplex coordinates. Its native coproduct
formula proves the actual pullback formula and the naturality of the
Alexander--Whitney product on original cochains.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual singular-simplex map induced by the original continuous map. -/
def simplexMap (f : C(X, Y)) (n : ℕ) : simplices X n → simplices Y n :=
  (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk n))

/-- The genuine singular-chain map sends a simplex to its actual image. -/
theorem chainMap_simplexChain (f : C(X, Y)) (n : ℕ) (s : simplices X n) :
    ((chainMap k f).f n).hom (simplexChain k X n s) =
      simplexChain k Y n (simplexMap f n s) := by
  have hcat :
      Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) s ≫ (chainMap k f).f n =
        Sigma.ι (fun _ : simplices Y n => ModuleCat.of k k) (simplexMap f n s) := by
    change Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) s ≫
      Sigma.map' (f := fun _ : simplices X n => ModuleCat.of k k)
        (g := fun _ : simplices Y n => ModuleCat.of k k)
        (simplexMap f n) (fun _ => 𝟙 (ModuleCat.of k k)) = _
    rw [Sigma.ι_comp_map', Category.id_comp]
  exact congrArg (fun g => g.hom 1) hcat

/-- Pullback on original cochains has the actual image-simplex values. -/
theorem values_cochainPullback (f : C(X, Y)) (n : ℕ)
    (a : cochains k Y n) (s : simplices X n) :
    values k X n (cochainPullback k f n a) s =
      values k Y n a (simplexMap f n s) := by
  change a (((chainMap k f).f n).hom (simplexChain k X n s)) = _
  rw [chainMap_simplexChain]
  rfl

/-- The original simplicial map commutes with each actual face. -/
theorem simplexMap_face (f : C(X, Y)) (n : ℕ) (i : Fin (n + 2))
    (s : simplices X (n + 1)) :
    simplexMap f n ((TopCat.toSSet.obj (TopCat.of X)).δ i s) =
      (TopCat.toSSet.obj (TopCat.of Y)).δ i (simplexMap f (n + 1) s) := by
  have h := (TopCat.toSSet.map (TopCat.ofHom f)).naturality (SimplexCategory.δ i).op
  exact congrFun h s

/-- The true degree-one Alexander--Whitney product commutes with actual pullback. -/
theorem cochainPullback_cupOne (f : C(X, Y)) (a b : cochains k Y 1) :
    cochainPullback k f 2 (cupOne k Y a b) =
      cupOne k X (cochainPullback k f 1 a) (cochainPullback k f 1 b) := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (cochainPullback k f 2 (cupOne k Y a b)) s =
    values k X 2 (cupOne k X (cochainPullback k f 1 a)
      (cochainPullback k f 1 b)) s
  rw [values_cochainPullback, values_cupOne, values_cupOne,
    values_cochainPullback, values_cochainPullback]
  simp only [edge, simplexMap_face]

end ChenRanks.SingularCohomology
