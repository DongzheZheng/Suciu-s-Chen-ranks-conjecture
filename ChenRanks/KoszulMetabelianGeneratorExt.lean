import ChenRanks.KoszulQuadraticMetabelianEquivalence

/-!
# Genuine original generators determine every original Koszul Lie morphism

The actual free Lie map to the actual original Koszul model is onto,
because its actual summed-ideal projection is onto and its proved actual
model equivalence is onto. The native free-Lie universal property then
proves that any two native Lie morphisms on the actual original model
agree once their actual original generator values agree.

This is a genuine uniqueness property of the constructed model. It
does not provide or assume any monodromy generator value or a Chen
comparison. Its later application must prove those generator values
on the same original objects.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k : Type*) [Field k] [CharZero k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

/-- The original free map is truly onto the original Koszul Lie model,
via its proved actual quotient equivalence. -/
theorem originalFreeLieToKoszulModel_surjective :
    Function.Surjective (freeLieToKoszulModel k V b K) := by
  letI : FiniteDimensional k V := _root_.Module.Finite.of_basis b
  intro x
  obtain ⟨y, hy⟩ := (quadraticMetabelianKoszulLieEquiv k V b K).surjective x
  obtain ⟨z, rfl⟩ := quadraticMetabelianProjection_surjective k V b K y
  refine ⟨z, ?_⟩
  change quadraticMetabelianToKoszulModelLinear k V b K
    (quadraticMetabelianProjection k V b K z) = x at hy
  rw [quadraticMetabelianToKoszulModelLinear_projection] at hy
  exact hy

variable {M : Type*} [LieRing M] [LieAlgebra k M]

include b

/-- Genuine native free-Lie uniqueness, applied through the actual
original onto map, determines maps on the entire original model. -/
theorem originalKoszulLieHom_ext
    (f g : Koszul.MetabelianLieModel k V K →ₗ⁅k⁆ M)
    (h : ∀ v : V, f (Koszul.MetabelianLieModel.generatorInclusion k V K v) =
      g (Koszul.MetabelianLieModel.generatorInclusion k V K v)) : f = g := by
  have hfree : f.comp (freeLieToKoszulModel k V b K) =
      g.comp (freeLieToKoszulModel k V b K) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change f (freeLieToKoszulModel k V b K (FreeLieAlgebra.of k i)) =
      g (freeLieToKoszulModel k V b K (FreeLieAlgebra.of k i))
    simp only [← freeVectorGenerators_basis k V b i, freeLieToKoszulModel_generator]
    exact h (b i)
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := originalFreeLieToKoszulModel_surjective k V b K x
  exact DFunLike.congr_fun hfree y

/-- A genuine post-composition comparison is proved by original
generator values; no preservation of the source grading is needed. -/
theorem originalKoszulLieHom_comp_eq_of_generators
    {N : Type*} [LieRing N] [LieAlgebra k N]
    (α : Koszul.MetabelianLieModel k V K →ₗ⁅k⁆ N)
    (ψ : N →ₗ⁅k⁆ M) (χ : Koszul.MetabelianLieModel k V K →ₗ⁅k⁆ M)
    (h : ∀ v : V,
      ψ (α (Koszul.MetabelianLieModel.generatorInclusion k V K v)) =
        χ (Koszul.MetabelianLieModel.generatorInclusion k V K v)) :
    ψ.comp α = χ :=
  originalKoszulLieHom_ext k V b K (ψ.comp α) χ h

end ChenRanks.LieComparison
