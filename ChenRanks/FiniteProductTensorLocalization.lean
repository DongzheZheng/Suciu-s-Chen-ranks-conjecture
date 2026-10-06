import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Native base change of a genuine finite family of module maps

The target is the actual finite product of the given original modules,
and the map is native base change of `LinearMap.pi`. Native tensor-Pi
equivalence proves the coordinate diagram. If one actual coordinate is
bijective and every other actual localized factor is zero, the native
base-changed finite-family map is bijective. The second theorem supplies
the case in which both source and all localized factors are zero.

These are generic tensor theorems; actual Koszul component hypotheses
must be discharged by the original separation and off-component
localization theorems when specializing them.
-/

open scoped TensorProduct

namespace ChenRanks

variable (S R : Type*) [CommRing S] [CommRing R] [Algebra S R]
variable (M : Type*) [AddCommGroup M] [Module S M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
variable (f : ∀ i, M →ₗ[S] N i)

/-- Every coordinate of the actual native finite-product base change
is the native base change of that original coordinate map. -/
theorem finiteProductTensor_baseChange_apply
    (z : R ⊗[S] M) (i : ι) :
    TensorProduct.piRight S R R N ((LinearMap.pi f).baseChange R z) i =
      (f i).baseChange R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | add z t hz ht => simp only [map_add, Pi.add_apply, hz, ht]
  | tmul r m =>
    simp only [LinearMap.baseChange_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, LinearMap.pi_apply]

/-- The native localization of the original family map is bijective
when one genuine localized coordinate is bijective and all the other
genuine localized factors are zero. -/
theorem finiteProductTensor_baseChange_bijective_of_one_component
    (i₀ : ι) (hi₀ : Function.Bijective ((f i₀).baseChange R))
    (hzero : ∀ i, i ≠ i₀ → Subsingleton (R ⊗[S] N i)) :
    Function.Bijective ((LinearMap.pi f).baseChange R) := by
  let e := TensorProduct.piRight S R R N
  let g : R ⊗[S] M → ∀ i, R ⊗[S] N i :=
    fun z => e ((LinearMap.pi f).baseChange R z)
  have hcoord : ∀ z i, g z i = (f i).baseChange R z :=
    finiteProductTensor_baseChange_apply S R M N f
  have hg : Function.Bijective g := by
    constructor
    · intro z t hzt
      apply hi₀.injective
      rw [← hcoord z i₀, ← hcoord t i₀, hzt]
    · intro y
      obtain ⟨z, hz⟩ := hi₀.surjective (y i₀)
      refine ⟨z, funext fun i => ?_⟩
      by_cases hi : i = i₀
      · subst i
        rw [hcoord z i₀, hz]
      · letI := hzero i hi
        exact Subsingleton.elim _ _
  constructor
  · intro z t hzt
    apply hg.injective
    exact congrArg e hzt
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (e y)
    exact ⟨z, e.injective hz⟩

/-- The zero-source case uses the same actual finite target product,
whose zero localization is derived by native tensor-Pi equivalence. -/
theorem finiteProductTensor_baseChange_bijective_of_subsingleton
    [Subsingleton (R ⊗[S] M)]
    (hzero : ∀ i, Subsingleton (R ⊗[S] N i)) :
    Function.Bijective ((LinearMap.pi f).baseChange R) := by
  have htarget : Subsingleton (R ⊗[S] ∀ i, N i) := by
    refine ⟨fun z t => (TensorProduct.piRight S R R N).injective ?_⟩
    apply funext
    intro i
    letI := hzero i
    exact Subsingleton.elim _ _
  letI := htarget
  constructor
  · intro z t _
    exact Subsingleton.elim _ _
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end ChenRanks
