import Mathlib.RingTheory.Localization.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual tensor localization killed by an actual denominator

An original scalar that kills the original module and belongs to the
actual denominator submonoid becomes a unit. Genuine tensor balancing
and the native unit action then force the literal tensor localization
to be zero. No finiteness, freeness, faithful action, or localized-zero
hypothesis is required.
-/

open scoped TensorProduct

namespace ChenRanks

variable (S R : Type*) [CommRing S] [CommRing R] [Algebra S R]
variable (D : Submonoid S) [IsLocalization D R]
variable (M : Type*) [AddCommGroup M] [Module S M]

/-- An actual annihilating denominator kills every element of the
literal native tensor localization. -/
theorem localizedTensor_eq_zero_of_annihilating_denominator
    (s : S) (hs : s ∈ D) (hsm : ∀ m : M, s • m = 0)
    (z : R ⊗[S] M) : z = 0 := by
  have hsz : algebraMap S R s • z = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
    | tmul r m =>
      rw [TensorProduct.smul_tmul']
      rw [IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul, hsm,
        TensorProduct.tmul_zero]
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨s, hs⟩ : D)
  have huz : (u : R) • z = 0 := by
    rw [hu]
    exact hsz
  have h := congrArg (fun t : R ⊗[S] M => (↑u⁻¹ : R) • t) huz
  simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using h

/-- The zero conclusion is about the full actual tensor type. -/
theorem localizedTensor_subsingleton_of_annihilating_denominator
    (s : S) (hs : s ∈ D) (hsm : ∀ m : M, s • m = 0) :
    Subsingleton (R ⊗[S] M) := by
  refine ⟨fun z t => ?_⟩
  exact (localizedTensor_eq_zero_of_annihilating_denominator S R D M s hs hsm z).trans
    (localizedTensor_eq_zero_of_annihilating_denominator S R D M s hs hsm t).symm

end ChenRanks
