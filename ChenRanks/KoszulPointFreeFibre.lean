import ChenRanks.KoszulPointPresentation
import ChenRanks.KoszulPointCokernel

/-!
# Cancellation of the actual free terms in the true point fibre

The original tensor fibre is identified with an actual exterior
presentation quotient by genuine tensor cancellation. The relation
source specializes surjectively, with explicit actual pure-tensor
preimages. At a nonzero point the previously proved exterior homotopy
then gives the actual contraction-kernel quotient.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V)) (a : V →ₗ[k] k)

variable (W : Type*) [AddCommGroup W] [_root_.Module k W]

/-- Actual free-term cancellation on an arbitrary original polynomial tensor. -/
theorem pointTensorCancel_eq_specialize (c : PointScalars k V a) (z : S k V ⊗[k] W) :
    pointTensorCancel k V W a (c ⊗ₜ[S k V] z) =
      pointScalarsEquiv k V a c • specializePolynomialTensor k V W a z := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw, smul_add]
  | tmul s w =>
    rw [pointTensorCancel_tmul, specializePolynomialTensor_tmul, smul_smul]

omit [AddCommGroup W] [_root_.Module k W] in
theorem specialize_delta3 (z : C3 k V) :
    specializePolynomialTensor k V (⋀[k]^2 V) a (delta3 k V z) =
      pointDeltaThree k V a (specializePolynomialTensor k V (⋀[k]^3 V) a z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s w =>
    rw [specialize_delta3_tmul, specializePolynomialTensor_tmul, map_smul]

omit [AddCommGroup W] [_root_.Module k W] in
theorem specialize_quadraticInclusion (z : S k V ⊗[k] K) :
    specializePolynomialTensor k V (⋀[k]^2 V) a (quadraticInclusion k V K z) =
      K.subtype (specializePolynomialTensor k V K a z) := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s w =>
    rw [quadraticInclusion_tmul, specializePolynomialTensor_tmul,
      specializePolynomialTensor_tmul, map_smul]
    rfl

omit [AddCommGroup W] [_root_.Module k W] in
/-- Specialize the genuine tensor relation source to the genuine exterior
and quadratic inputs, via the actual two free-term cancellation maps. -/
def pointRelationSourceSpecialize :
    (PointScalars k V a ⊗[S k V] (C3 k V × (S k V ⊗[k] K))) →ₗ[k]
      ((⋀[k]^3 V) × K) :=
  ((pointTensorCancel k V (⋀[k]^3 V) a).toLinearMap.comp
    ((AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
      (LinearMap.fst (S k V) (C3 k V) (S k V ⊗[k] K))).restrictScalars k)).prod
  ((pointTensorCancel k V K a).toLinearMap.comp
    ((AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
      (LinearMap.snd (S k V) (C3 k V) (S k V ⊗[k] K))).restrictScalars k))

omit [AddCommGroup W] [_root_.Module k W] in
@[simp] theorem pointRelationSourceSpecialize_tmul (c : PointScalars k V a)
    (y : C3 k V) (x : S k V ⊗[k] K) :
    pointRelationSourceSpecialize k V K a (c ⊗ₜ[S k V] (y, x)) =
      (pointScalarsEquiv k V a c • specializePolynomialTensor k V (⋀[k]^3 V) a y,
        pointScalarsEquiv k V a c • specializePolynomialTensor k V K a x) := by
  change
    (pointTensorCancel k V (⋀[k]^3 V) a
        ((AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
          (LinearMap.fst (S k V) (C3 k V) (S k V ⊗[k] K)))
            (c ⊗ₜ[S k V] (y, x))),
      pointTensorCancel k V K a
        ((AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
          (LinearMap.snd (S k V) (C3 k V) (S k V ⊗[k] K)))
            (c ⊗ₜ[S k V] (y, x)))) = _
  apply Prod.ext
  · rw [AlgebraTensorModule.lTensor_tmul, LinearMap.fst_apply]
    exact pointTensorCancel_eq_specialize k V (W := ↥(⋀[k]^3 V)) a c y
  · change pointTensorCancel k V K a
      ((AlgebraTensorModule.lTensor (PointScalars k V a) (PointScalars k V a)
        (LinearMap.snd (S k V) (C3 k V) (S k V ⊗[k] K)))
          (c ⊗ₜ[S k V] (y, x))) =
        pointScalarsEquiv k V a c • specializePolynomialTensor k V K a x
    rw [AlgebraTensorModule.lTensor_tmul, LinearMap.snd_apply]
    exact pointTensorCancel_eq_specialize k V (W := K) a c x

omit [AddCommGroup W] [_root_.Module k W] in
/-- Surjectivity uses actual constant polynomial tensors; no arbitrary
specialization or fibre-surjectivity premise is supplied. -/
theorem pointRelationSourceSpecialize_surjective :
    Function.Surjective (pointRelationSourceSpecialize k V K a) := by
  rintro ⟨w, x⟩
  refine ⟨(1 : PointScalars k V a) ⊗ₜ[S k V]
    ((1 : S k V) ⊗ₜ[k] w, (1 : S k V) ⊗ₜ[k] x), ?_⟩
  simp only [pointRelationSourceSpecialize_tmul, map_one,
    specializePolynomialTensor_tmul, one_smul]

omit [AddCommGroup W] [_root_.Module k W] in
/-- The genuine tensor-extended presentation relation followed by actual
free-term cancellation. -/
def pointFreeRelationMap :
    (PointScalars k V a ⊗[S k V] (C3 k V × (S k V ⊗[k] K))) →ₗ[k] (⋀[k]^2 V) :=
  (pointTensorCancel k V (⋀[k]^2 V) a).toLinearMap.comp
    ((pointPresentationRelationExtension k V K a).restrictScalars k)

omit [AddCommGroup W] [_root_.Module k W] in
/-- The original presentation specializes to the actual third contraction
and actual quadratic inclusion, with the genuine source map above. -/
theorem pointFreeRelationMap_eq :
    pointFreeRelationMap k V K a =
      (pointThirdQuadraticRelations k V K a).comp
        (pointRelationSourceSpecialize k V K a) := by
  apply LinearMap.ext
  intro z
  induction z with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c z =>
    rcases z with ⟨y, x⟩
    simp only [pointFreeRelationMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      pointPresentationRelationExtension, AlgebraTensorModule.lTensor_tmul,
      LinearEquiv.coe_toLinearMap, pointTensorCancel_eq_specialize,
      presentationRelations_apply, map_add, specialize_delta3,
      specialize_quadraticInclusion, smul_add,
      pointThirdQuadraticRelations, LinearMap.coprod_apply,
      pointRelationSourceSpecialize_tmul, map_smul]

omit [AddCommGroup W] [_root_.Module k W] in
/-- The true cancelled relation image is the true point contraction plus
quadratic relation image, because the genuine source specialization is
surjective. -/
theorem pointPresentationRelationExtension_map_range :
    Submodule.map (pointTensorCancel k V (⋀[k]^2 V) a).toLinearMap
        ((LinearMap.range (pointPresentationRelationExtension k V K a)).restrictScalars k) =
      LinearMap.range (pointThirdQuadraticRelations k V K a) := by
  rw [← LinearMap.range_restrictScalars, ← LinearMap.range_comp]
  change LinearMap.range (pointFreeRelationMap k V K a) = _
  rw [pointFreeRelationMap_eq, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (pointRelationSourceSpecialize_surjective k V K a))]

variable [FiniteDimensional k V] [CharZero k]

omit [AddCommGroup W] [_root_.Module k W] in
/-- A proved identification of the literal original tensor fibre with the
actual exterior presentation quotient, using genuine tensor cancellation. -/
def pointFibreExteriorEquiv :
    PointFiber k V K a ≃ₗ[k]
      ((⋀[k]^2 V) ⧸ LinearMap.range (pointThirdQuadraticRelations k V K a)) :=
  (pointPresentationCokerEquiv k V K a).trans
    (Submodule.Quotient.equiv _ _ (pointTensorCancel k V (⋀[k]^2 V) a)
      (pointPresentationRelationExtension_map_range k V K a))

omit [AddCommGroup W] [_root_.Module k W] in
/-- The actual nonzero-point fibre of the original module is proved
equivalent to the actual contraction-kernel quotient. -/
def pointFibreContractionEquiv (ha : a ≠ 0) :
    PointFiber k V K a ≃ₗ[k]
      (LinearMap.ker a ⧸ LinearMap.range (pointQuadraticRelation k V K a)) :=
  (pointFibreExteriorEquiv k V K a).trans (pointContractionCokerEquiv k V K a ha)

end ChenRanks.Koszul
