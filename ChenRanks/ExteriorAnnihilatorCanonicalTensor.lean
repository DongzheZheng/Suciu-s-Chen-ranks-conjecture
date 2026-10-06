import ChenRanks.CanonicalAnnihilatorTensor
import ChenRanks.KoszulComponentDuality

/-!
# Actual exterior determinant duality gives the actual curvature tensor

The original coordinate functionals of the actual exterior basis are
identified with the actual exterior products of the original coordinate
functionals. The identification uses the already proved native determinant
pairing. Thus complementary quadratic kernel/annihilator containments
give the genuine finite sum of original wedge/bracket coefficients.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

variable {k E X Y : Type*} [Field k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]
variable {κ : Type*} [Fintype κ] [LinearOrder κ]

/-- Actual exterior basis dual coordinates have their actual determinant
representatives, rather than an arbitrary chosen duality. -/
theorem exteriorPairingDualEquiv_symm_basis_coord
    (b : Module.Basis κ k E) (s : Set.powersetCard κ 2) :
    (Koszul.exteriorPairingDualEquiv k E 2).symm ((b.exteriorPower 2).coord s) =
      exteriorPower.ιMulti_family k 2 b.coord s := by
  apply (Koszul.exteriorPairingDualEquiv k E 2).injective
  rw [LinearEquiv.apply_symm_apply]
  change (b.exteriorPower 2).coord s = exteriorPower.ιMultiDual k 2 b s
  exact exteriorPower.basis_coord k 2 b s

/-- The true original wedge/co-bracket sum vanishes from true complementary
quadratic containments. This is a derived tensor identity. -/
theorem sum_exterior_basis_tmul_dual_eq_zero_of_annihilator
    (b : Module.Basis κ k E) (I : Submodule k (⋀[k]^2 E))
    (α : (⋀[k]^2 E) →ₗ[k] X)
    (β : (⋀[k]^2 (Module.Dual k E)) →ₗ[k] Y)
    (hα : I ≤ LinearMap.ker α)
    (hβ : Koszul.exteriorAnnihilator k E 2 I ≤ LinearMap.ker β) :
    (∑ s : Set.powersetCard κ 2,
      α (b.exteriorPower 2 s) ⊗ₜ[k]
        β (exteriorPower.ιMulti_family k 2 b.coord s)) = 0 := by
  let e := Koszul.exteriorPairingDualEquiv k E 2
  let qβ := β.comp e.symm.toLinearMap
  have hqβ : I.dualAnnihilator ≤ LinearMap.ker qβ := by
    intro φ hφ
    change β (e.symm φ) = 0
    apply hβ
    change exteriorPower.pairingDual k E 2 (e.symm φ) ∈ I.dualAnnihilator
    have he : exteriorPower.pairingDual k E 2 (e.symm φ) = φ := e.apply_symm_apply φ
    rw [he]
    exact hφ
  have h := canonicalImageTensor_eq_zero_of_annihilator
    (b.exteriorPower 2) I α qβ hα hqβ
  have hc (s : Set.powersetCard κ 2) :
      qβ ((b.exteriorPower 2).coord s) =
        β (exteriorPower.ιMulti_family k 2 b.coord s) := by
    change β (e.symm ((b.exteriorPower 2).coord s)) = _
    rw [exteriorPairingDualEquiv_symm_basis_coord b s]
  simpa only [canonicalImageTensor, hc] using h

end ChenRanks
