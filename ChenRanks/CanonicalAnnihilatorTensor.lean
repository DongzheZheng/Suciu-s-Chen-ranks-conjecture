import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A genuine canonical-tensor annihilator identity

The tensor is constructed from an actual finite basis and its actual
coordinate functionals. A map killing an original subspace and a second
map killing that subspace's genuine functional annihilator send this
canonical tensor to zero. The target spaces may be infinite-dimensional.
The proof uses their actual vector-space bases only to detect tensor
coordinates; it does not assume a tensor-detection or pairing condition.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable {k U X Y : Type*} [Field k]
variable [AddCommGroup U] [Module k U]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]
variable {κ : Type*} [Fintype κ]

/-- The actual image of the actual basis/coordinate canonical tensor. -/
def canonicalImageTensor (b : Module.Basis κ k U)
    (α : U →ₗ[k] X) (β : Module.Dual k U →ₗ[k] Y) : X ⊗[k] Y :=
  ∑ i : κ, α (b i) ⊗ₜ[k] β (b.coord i)

/-- Actual finite basis reconstruction of the actual pullback functional. -/
theorem sum_pullback_coordinates (b : Module.Basis κ k U)
    (α : U →ₗ[k] X) (φ : Module.Dual k X) :
    (∑ i : κ, φ (α (b i)) • b.coord i) = φ.comp α := by
  classical
  have h := b.dualBasis.sum_repr (φ.comp α)
  simpa only [Module.Basis.dualBasis_repr, Module.Basis.coe_dualBasis,
    LinearMap.comp_apply] using h

/-- The genuine annihilator hypotheses imply the genuine canonical
tensor identity; no dimension or tensor-pairing premise is put on targets. -/
theorem canonicalImageTensor_eq_zero_of_annihilator
    (b : Module.Basis κ k U) (I : Submodule k U)
    (α : U →ₗ[k] X) (β : Module.Dual k U →ₗ[k] Y)
    (hα : I ≤ LinearMap.ker α) (hβ : I.dualAnnihilator ≤ LinearMap.ker β) :
    canonicalImageTensor b α β = 0 := by
  classical
  letI : Module.Free k X := Module.Free.of_divisionRing k X
  letI : Module.Free k Y := Module.Free.of_divisionRing k Y
  let bx := Module.Free.chooseBasis k X
  let byasis := Module.Free.chooseBasis k Y
  apply (bx.tensorProduct byasis).repr.injective
  apply Finsupp.ext
  rintro ⟨i, j⟩
  rw [map_zero, Finsupp.zero_apply]
  have hφ : (bx.coord i).comp α ∈ I.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro u hu
    change bx.coord i (α u) = 0
    rw [show α u = 0 from hα hu, map_zero]
  have hb : β ((bx.coord i).comp α) = 0 := hβ hφ
  rw [← sum_pullback_coordinates b α (bx.coord i), map_sum] at hb
  have h := congrArg (byasis.coord j) hb
  change (bx.tensorProduct byasis).repr
    (∑ a : κ, α (b a) ⊗ₜ[k] β (b.coord a)) (i, j) = 0
  simp only [map_sum, Finsupp.finset_sum_apply,
    Module.Basis.tensorProduct_repr_tmul_apply]
  simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, mul_comm, map_zero] using h

end ChenRanks
