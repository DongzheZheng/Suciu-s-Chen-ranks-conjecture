import ChenRanks.KoszulPolynomialHomotopy
import ChenRanks.KoszulThirdObjects

/-!
# Genuine coefficient evaluation and pointwise Koszul contraction

A point of the dual generator space gives the actual symmetric-algebra
evaluation map.  Its tensor evaluation specializes the original second
differential.  At every nonzero point its actual image is the actual
kernel of the point functional.  This is a step toward a fibre comparison,
not a definition of the fibre of the original quotient module.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

/-- The actual polynomial evaluation defined by a point of the true dual space. -/
def pointEvaluation (a : V →ₗ[k] k) : S k V →ₐ[k] k := SymmetricAlgebra.lift a

@[simp] theorem pointEvaluation_generator (a : V →ₗ[k] k) (v : V) :
    pointEvaluation k V a (SymmetricAlgebra.ι k V v) = a v := by
  simp [pointEvaluation]

variable (W : Type*) [AddCommGroup W] [_root_.Module k W]

/-- Evaluate the actual coefficient factor of the genuine tensor product. -/
def specializePolynomialTensor (a : V →ₗ[k] k) : S k V ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap.comp ((pointEvaluation k V a).toLinearMap.rTensor W)

@[simp] theorem specializePolynomialTensor_tmul (a : V →ₗ[k] k)
    (s : S k V) (w : W) :
    specializePolynomialTensor k V W a (s ⊗ₜ[k] w) = pointEvaluation k V a s • w := by
  simp [specializePolynomialTensor]

/-- The actual polynomial scalar action specializes to the actual evaluated scalar. -/
theorem specializePolynomialTensor_smul (a : V →ₗ[k] k)
    (s : S k V) (z : S k V ⊗[k] W) :
    specializePolynomialTensor k V W a (s • z) =
      pointEvaluation k V a s • specializePolynomialTensor k V W a z := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  | tmul t w =>
    rw [TensorProduct.smul_tmul', specializePolynomialTensor_tmul]
    simp only [smul_eq_mul, map_mul, specializePolynomialTensor_tmul, smul_smul]

omit [AddCommGroup W] [_root_.Module k W] in
/-- The genuine point contraction is obtained by evaluating the original
second Koszul differential on its actual constant exterior input. -/
def pointDeltaTwo (a : V →ₗ[k] k) : (⋀[k]^2 V) →ₗ[k] V :=
  (specializePolynomialTensor k V V a).comp (delta2Linear k V)

omit [AddCommGroup W] [_root_.Module k W] in
@[simp] theorem pointDeltaTwo_wedge (a : V →ₗ[k] k) (u v : V) :
    pointDeltaTwo k V a (exteriorWedge u v) = a u • v - a v • u := by
  simp only [pointDeltaTwo, LinearMap.comp_apply, delta2Linear_exteriorWedge,
    map_sub, specializePolynomialTensor_smul, specializePolynomialTensor_tmul,
    map_one, pointEvaluation_generator, one_smul]

omit [AddCommGroup W] [_root_.Module k W] in
/-- Specializing the original polynomial differential gives the actual contraction,
with the evaluated polynomial scalar. -/
theorem specialize_delta2_tmul (a : V →ₗ[k] k) (s : S k V) (w : ⋀[k]^2 V) :
    specializePolynomialTensor k V V a (delta2 k V (s ⊗ₜ[k] w)) =
      pointEvaluation k V a s • pointDeltaTwo k V a w := by
  rw [delta2_tmul, specializePolynomialTensor_smul]
  rfl

omit [AddCommGroup W] [_root_.Module k W] in
theorem pointEvaluation_comp_pointDeltaTwo (a : V →ₗ[k] k) :
    a.comp (pointDeltaTwo k V a) = 0 := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : exteriorPower.ιMulti k 2 v = exteriorWedge (v 0) (v 1) := by
    change exteriorPower.ιMulti k 2 v = exteriorPower.ιMulti k 2 ![v 0, v 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, hv,
    pointDeltaTwo_wedge, map_sub, map_smul, smul_eq_mul, LinearMap.zero_apply]
  ring

omit [AddCommGroup W] [_root_.Module k W] in
/-- A nonzero actual point functional has an actual normalized vector. -/
theorem exists_point_normalized_vector (a : V →ₗ[k] k) (ha : a ≠ 0) :
    ∃ v : V, a v = 1 := by
  obtain ⟨v, hv⟩ : ∃ v : V, a v ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    ext v
    exact h v
  refine ⟨(a v)⁻¹ • v, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]

omit [AddCommGroup W] [_root_.Module k W] in
/-- Exactness of the actual point contraction away from the origin.
The exterior preimage is the genuine wedge with a normalized vector. -/
theorem pointDeltaTwo_range_eq_ker (a : V →ₗ[k] k) (ha : a ≠ 0) :
    LinearMap.range (pointDeltaTwo k V a) = LinearMap.ker a := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact DFunLike.congr_fun (pointEvaluation_comp_pointDeltaTwo k V a) w
  · intro v hv
    obtain ⟨u, hu⟩ := exists_point_normalized_vector k V a ha
    refine ⟨exteriorWedge u v, ?_⟩
    have hv0 : a v = 0 := LinearMap.mem_ker.mp hv
    rw [pointDeltaTwo_wedge, hu, hv0, one_smul, zero_smul, sub_zero]

end ChenRanks.Koszul
