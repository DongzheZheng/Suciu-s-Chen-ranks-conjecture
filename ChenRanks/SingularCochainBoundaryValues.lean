import ChenRanks.SingularSimplexCochains

/-!
# The genuine singular coboundary on genuine simplex values

The face-sum formula is derived from the library's alternating-face
singular chain boundary and native coproduct maps. It is not supplied as
an axiom identifying an independently chosen cochain model.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped BigOperators

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The actual coefficient diagram underlying the native singular chains. -/
def coefficientDiagram : SimplicialObject (ModuleCat.{0} k) :=
  TopCat.toSSet.obj (TopCat.of X) ⋙ sigmaConst.obj (ModuleCat.of k k)

/-- The native alternating singular boundary sends an actual simplex
to the actual signed sum of its faces. -/
theorem boundary_simplexChain (n : ℕ) (s : simplices X (n + 1)) :
    ((chains k X).d (n + 1) n).hom (simplexChain k X (n + 1) s) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        simplexChain k X n ((TopCat.toSSet.obj (TopCat.of X)).δ i s) := by
  let T := TopCat.toSSet.obj (TopCat.of X)
  have hcat :
      Sigma.ι (fun _ : simplices X (n + 1) => ModuleCat.of k k) s ≫
        AlternatingFaceMapComplex.objD (coefficientDiagram k X) n =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) (T.δ i s) := by
    rw [AlternatingFaceMapComplex.objD]
    calc
      _ = ∑ i : Fin (n + 2),
          Sigma.ι (fun _ : simplices X (n + 1) => ModuleCat.of k k) s ≫
            (((-1 : ℤ) ^ (i : ℕ)) • (coefficientDiagram k X).δ i) :=
        map_sum (Preadditive.leftComp _
          (Sigma.ι (fun _ : simplices X (n + 1) => ModuleCat.of k k) s)) _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        erw [Preadditive.comp_zsmul]
        congr 1
        simp [coefficientDiagram, SimplicialObject.δ, sigmaConst, T]
  have h1 := congrArg (fun f => f.hom 1) hcat
  let ev : (ModuleCat.of k k ⟶ (chains k X).X n) →+ (chains k X).X n :=
    { toFun := fun f => f.hom 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsum :
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) (T.δ i s)).hom 1 =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) (T.δ i s)).hom 1 := by
    change ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) (T.δ i s)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_zsmul ev _ _
  have h2 := h1.trans hsum
  change (((alternatingFaceMapComplex (ModuleCat.{0} k)).obj
      (coefficientDiagram k X)).d (n + 1) n).hom
    ((Sigma.ι (fun _ : simplices X (n + 1) => ModuleCat.of k k) s).hom 1) = _
  rw [alternatingFaceMapComplex_obj_d]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, simplexChain] using h2

/-- The original dual boundary has the exact original signed face values. -/
theorem values_differential (n : ℕ) (a : cochains k X n)
    (s : simplices X (n + 1)) :
    values k X (n + 1) (differential k X n a) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        values k X n a ((TopCat.toSSet.obj (TopCat.of X)).δ i s) := by
  change a (((chains k X).d (n + 1) n).hom (simplexChain k X (n + 1) s)) = _
  rw [boundary_simplexChain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact map_zsmul a _ _

end ChenRanks.SingularCohomology
