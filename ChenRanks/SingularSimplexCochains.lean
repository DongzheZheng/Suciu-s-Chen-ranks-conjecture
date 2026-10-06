import ChenRanks.ArrangementSingularCohomology

/-!
# Values of genuine singular cochains on genuine simplices

The singular chain module is the native coproduct of copies of the
coefficient field indexed by the actual singular simplices. Its universal
property identifies its linear dual with all functions on those simplices.
This supplies concrete cochain coordinates for the later cup-product
construction without replacing the original chain complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The actual singular simplices of the original space in degree n. -/
abbrev simplices (n : ℕ) :=
  (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n))

/-- The native inclusion of a genuine simplex as its singular chain. -/
def simplexChain (n : ℕ) (s : simplices X n) : (chains k X).X n :=
  (Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) s).hom 1

/-- Evaluation of an actual linear cochain on all genuine singular simplices. -/
def values (n : ℕ) : cochains k X n →ₗ[k] (simplices X n → k) where
  toFun ℓ s := ℓ (simplexChain k X n s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coproduct universal property extends any actual simplex values. -/
def ofValues (n : ℕ) (a : simplices X n → k) : cochains k X n :=
  (Sigma.desc (fun s : simplices X n =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton k k (a s)))).hom

/-- Actual simplex inclusions determine every original cochain. -/
theorem cochain_ext (n : ℕ) (ℓ m : cochains k X n)
    (h : ∀ s, ℓ (simplexChain k X n s) = m (simplexChain k X n s)) : ℓ = m := by
  have hcat : ModuleCat.ofHom ℓ = ModuleCat.ofHom m := by
    apply Sigma.hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let ι := Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) s
    have ha : ι.hom a = a • ι.hom 1 := by
      rw [← map_smul]
      simp
    change ℓ (ι.hom a) = m (ι.hom a)
    rw [ha]
    exact (ℓ.map_smul a _).trans
      ((congrArg (fun z : k => a • z) (h s)).trans (m.map_smul a _).symm)
  exact congrArg (fun f => f.hom) hcat

/-- The constructed extension has precisely the original simplex values. -/
theorem values_ofValues (n : ℕ) (a : simplices X n → k) :
    values k X n (ofValues k X n a) = a := by
  funext s
  have h := Sigma.ι_desc
    (fun t : simplices X n => ModuleCat.ofHom (LinearMap.toSpanSingleton k k (a t))) s
  have h1 := congrArg (fun f => f.hom 1) h
  change (Sigma.desc (fun t : simplices X n =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton k k (a t)))).hom
      ((Sigma.ι (fun _ : simplices X n => ModuleCat.of k k) s).hom 1) = a s
  simpa using h1

/-- The extension also recovers the original linear cochain, not just its values. -/
theorem ofValues_values (n : ℕ) (ℓ : cochains k X n) :
    ofValues k X n (values k X n ℓ) = ℓ := by
  apply cochain_ext k X n
  intro s
  exact congrFun (values_ofValues k X n (values k X n ℓ)) s

/-- The genuine linear equivalence between cochains and actual simplex functions. -/
def valuesEquiv (n : ℕ) : cochains k X n ≃ₗ[k] (simplices X n → k) where
  toLinearMap := values k X n
  invFun := ofValues k X n
  left_inv := ofValues_values k X n
  right_inv := values_ofValues k X n

end ChenRanks.SingularCohomology
