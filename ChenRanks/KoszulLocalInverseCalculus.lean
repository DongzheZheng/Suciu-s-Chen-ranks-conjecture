import ChenRanks.KoszulIsotropicComponentLocalMaps
import ChenRanks.KoszulLocalProjectionClasses

/-!
# Generic calculus for the genuine local component inverse

These bounded proofs operate on actual original Koszul maps and actual
tensor products. Their scalar and exterior correction hypotheses are
intermediate identities, separately derived from separation in the
actual component application. No local isomorphism is an input.

Second-term surjectivity is derived from the already proved actual
Koszul exactness theorem, rather than introduced as an assumption.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

private theorem secondTerm_scalar_tensor_formula
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R]
    (s : S k V) (w : ⋀[k]^2 V) :
    coefficientExtendedSecondMap k V K R (s ⊗ₜ[k] w) =
      algebraMap (S k V) R s • coefficientExtendedExteriorClass k V K R w := by
  have hs : s ⊗ₜ[k] w = s • ((1 : S k V) ⊗ₜ[k] w) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, coefficientExtendedSecondMap_smul]
  rfl

/-- Genuine scalar and exterior corrections extend by actual tensor
induction to every second-term presentation class. -/
theorem secondTensor_projection_correction
    (k : Type*) [Field k]
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [_root_.Module k V] [_root_.Module k W]
    (K : Submodule k (⋀[k]^2 V)) (f : V →ₗ[k] W) (g : W →ₗ[k] V)
    (R : Type*) [CommRing R] [Algebra (S k V) R]
    (hscalar : ∀ (s : S k V) (z : CoefficientExtendedModule k V K R),
      algebraMap (S k V) R (symmetricMap k W V g (symmetricMap k V W f s)) • z =
        algebraMap (S k V) R s • z)
    (hexterior : ∀ w : ⋀[k]^2 V,
      coefficientExtendedExteriorClass k V K R (exteriorPower.map 2 (g.comp f) w) =
        coefficientExtendedExteriorClass k V K R w)
    (z : C2 k V) :
    coefficientExtendedSecondMap k V K R
      (tensorTwoMap k W V g (tensorTwoMap k V W f z)) =
      coefficientExtendedSecondMap k V K R z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(tensorTwoMap k V W f).map_zero,
      (tensorTwoMap k W V g).map_zero]
  | add z t hz ht => rw [(tensorTwoMap k V W f).map_add,
      (tensorTwoMap k W V g).map_add,
      (coefficientExtendedSecondMap k V K R).map_add,
      (coefficientExtendedSecondMap k V K R).map_add, hz, ht]
  | tmul s w =>
    simp only [tensorTwoMap, TensorProduct.map_tmul]
    have hw : exteriorPower.map 2 g (exteriorPower.map 2 f w) =
        exteriorPower.map 2 (g.comp f) w := by
      rw [exteriorPower.map_comp, LinearMap.comp_apply]
    rw [hw, secondTerm_scalar_tensor_formula, secondTerm_scalar_tensor_formula,
      hexterior]
    exact hscalar s _

/-- Naturality of the actual quotient maps and the genuine second-term
correction prove the localized correction on all presentation classes. -/
theorem quotient_secondClass_projection_correction
    (k : Type*) [Field k]
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [_root_.Module k V] [_root_.Module k W]
    (K : Submodule k (⋀[k]^2 V)) (L : Submodule k (⋀[k]^2 W))
    (f : V →ₗ[k] W) (g : W →ₗ[k] V)
    (hf : K ≤ L.comap (exteriorPower.map 2 f))
    (hg : L ≤ K.comap (exteriorPower.map 2 g))
    (R : Type*) [CommRing R] [Algebra (S k V) R]
    (hscalar : ∀ (s : S k V) (z : CoefficientExtendedModule k V K R),
      algebraMap (S k V) R (symmetricMap k W V g (symmetricMap k V W f s)) • z =
        algebraMap (S k V) R s • z)
    (hexterior : ∀ w : ⋀[k]^2 V,
      coefficientExtendedExteriorClass k V K R (exteriorPower.map 2 (g.comp f) w) =
        coefficientExtendedExteriorClass k V K R w)
    (z : C2 k V) :
    (1 : R) ⊗ₜ[S k V]
      moduleMap k W V g L K hg (moduleMap k V W f K L hf
        (secondTensorToModule k V K z)) = coefficientExtendedSecondMap k V K R z := by
  rw [moduleMap_secondTensorToModule, moduleMap_secondTensorToModule]
  exact secondTensor_projection_correction k V W K f g R hscalar hexterior z

/-- The already proved actual second-term surjection extends the true
presentation-class correction to every element of the original quotient. -/
theorem quotient_constantTensor_projection_correction
    (k : Type*) [Field k] [CharZero k]
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [_root_.Module k V] [_root_.Module k W] [FiniteDimensional k V]
    (K : Submodule k (⋀[k]^2 V)) (L : Submodule k (⋀[k]^2 W))
    (f : V →ₗ[k] W) (g : W →ₗ[k] V)
    (hf : K ≤ L.comap (exteriorPower.map 2 f))
    (hg : L ≤ K.comap (exteriorPower.map 2 g))
    (R : Type*) [CommRing R] [Algebra (S k V) R]
    (hcorrection : ∀ z : C2 k V, (1 : R) ⊗ₜ[S k V]
      moduleMap k W V g L K hg (moduleMap k V W f K L hf
        (secondTensorToModule k V K z)) = coefficientExtendedSecondMap k V K R z)
    (z : Module k V K) :
    (1 : R) ⊗ₜ[S k V]
      moduleMapSemilinear k W V g L K hg
        (moduleMapSemilinear k V W f K L hf z) = (1 : R) ⊗ₜ[S k V] z := by
  obtain ⟨t, rfl⟩ := secondTensorToModule_surjective k V K z
  exact hcorrection t

/-- A tensor inverse follows from the true constant-tensor correction
and the true whole coefficient action, by native tensor induction. -/
theorem semilinearTensorMap_inverse_apply
    (S T R A : Type*) [CommRing S] [CommRing T] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra T A]
    (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [_root_.Module S M] [_root_.Module T N]
    (φ : S →+* T) (ψ : T →+* S)
    (F : R →ₛₗ[φ] A) (G : M →ₛₗ[φ] N)
    (F' : A →ₛₗ[ψ] R) (G' : N →ₛₗ[ψ] M)
    (hconstant : ∀ m : M,
      (1 : R) ⊗ₜ[S] G' (G m) = (1 : R) ⊗ₜ[S] m)
    (haction : ∀ (r : R) (z : R ⊗[S] M), F' (F r) • z = r • z)
    (z : R ⊗[S] M) :
    TensorProduct.map F' G' (TensorProduct.map F G z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z t hz ht => rw [map_add, map_add, hz, ht]
  | tmul r m =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    have hleft : F' (F r) ⊗ₜ[S] G' (G m) =
        F' (F r) • ((1 : R) ⊗ₜ[S] G' (G m)) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hright : r ⊗ₜ[S] m = r • ((1 : R) ⊗ₜ[S] m) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hleft, hright, hconstant]
    exact haction r _

end ChenRanks.Koszul
