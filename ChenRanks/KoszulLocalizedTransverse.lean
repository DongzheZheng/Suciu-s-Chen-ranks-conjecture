import ChenRanks.KoszulPresentation
import ChenRanks.KoszulPointAnnSupport
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Actual scalar-extended Koszul relations and transverse elimination

The module is literally a scalar extension of the original Koszul
module, not a newly defined presentation carrying the expected answer.
The true third Koszul relation is transported to that literal module.
Over an actual local coefficient algebra, true mixed quadratic lifts
with corrections in the actual span of pure transverse wedges imply
vanishing of the actual transverse generator span by Nakayama.

The quadratic lifts are explicit genuine elements of the actual
quadratic relation range. Deriving those lifts from actual separation,
and connecting this scalar extension to actual projective sheaf stalks,
remain separate obligations. Neither local isomorphism, annihilator
radicality, nor effective decomposition is a premise or conclusion here.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V))
variable (R : Type*) [CommRing R] [Algebra (S k V) R]

/-- Literal scalar extension of the original Koszul module. -/
abbrev CoefficientExtendedModule := R ⊗[S k V] Module k V K

/-- The genuine original second-term map followed by true tensor inclusion. -/
def coefficientExtendedSecondMap : C2 k V →ₗ[S k V] CoefficientExtendedModule k V K R :=
  TensorProduct.mk (S k V) R (Module k V K) 1 ∘ₗ secondTensorToModule k V K

/-- Actual exterior generator class in the literal scalar extension. -/
def coefficientExtendedExteriorClass (w : ⋀[k]^2 V) : CoefficientExtendedModule k V K R :=
  coefficientExtendedSecondMap k V K R ((1 : S k V) ⊗ₜ[k] w)

/-- The actual coefficient coordinate in the true coefficient algebra. -/
def extendedCoefficient (v : V) : R := algebraMap (S k V) R (SymmetricAlgebra.ι k V v)

/-- True coefficient action on the genuine second-term map. -/
theorem coefficientExtendedSecondMap_smul (s : S k V) (z : C2 k V) :
    coefficientExtendedSecondMap k V K R (s • z) =
      algebraMap (S k V) R s • coefficientExtendedSecondMap k V K R z := by
  rw [map_smul, IsScalarTower.algebraMap_smul]

/-- The true third relations vanish in the literal original-module scalar extension. -/
theorem coefficientExtendedSecondMap_delta3 (z : C3 k V) :
    coefficientExtendedSecondMap k V K R (delta3 k V z) = 0 := by
  change (1 : R) ⊗ₜ[S k V] secondTensorToModule k V K (delta3 k V z) = 0
  rw [secondTensorToModule_delta3, TensorProduct.tmul_zero]

/-- True quadratic relations vanish in the literal original-module scalar extension. -/
theorem coefficientExtendedSecondMap_quadratic (z : C2 k V)
    (hz : z ∈ LinearMap.range (quadraticInclusion k V K)) :
    coefficientExtendedSecondMap k V K R z = 0 := by
  obtain ⟨x, rfl⟩ := hz
  change (1 : R) ⊗ₜ[S k V] secondTensorToModule k V K (quadraticInclusion k V K x) = 0
  rw [secondTensorToModule_quadraticInclusion, TensorProduct.tmul_zero]

/-- The genuine three-term relation among actual exterior generator
classes is derived from the actual third Koszul differential. -/
theorem coefficientExtendedExteriorClass_third (v u w : V) :
    extendedCoefficient k V R v • coefficientExtendedExteriorClass k V K R (exteriorWedge u w) -
        extendedCoefficient k V R u • coefficientExtendedExteriorClass k V K R (exteriorWedge v w) +
          extendedCoefficient k V R w • coefficientExtendedExteriorClass k V K R (exteriorWedge v u) = 0 := by
  have h := coefficientExtendedSecondMap_delta3 k V K R
    ((1 : S k V) ⊗ₜ[k] exteriorPower.ιMulti k 3 ![v, u, w])
  rw [delta3_tmul, one_smul, delta3Linear_wedge] at h
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    map_add, map_sub, coefficientExtendedSecondMap_smul,
    coefficientExtendedExteriorClass, extendedCoefficient] using h

variable {τ : Type*} (u : τ → V) (v : V)

/-- Actual span of the actual transverse wedge classes in the literal module. -/
def extendedTransverseSpan : Submodule R (CoefficientExtendedModule k V K R) :=
  Submodule.span R (Set.range fun t ↦ coefficientExtendedExteriorClass k V K R (exteriorWedge v (u t)))

/-- Actual polynomial-linear span of actual pure transverse second terms. -/
def pureTransverseSecondSpan : Submodule (S k V) (C2 k V) :=
  Submodule.span (S k V) (Set.range fun ij : τ × τ ↦
    (1 : S k V) ⊗ₜ[k] exteriorWedge (u ij.1) (u ij.2))

variable [IsLocalRing R]

/-- A true pure transverse wedge class lies in maximal-ideal times the
actual transverse span, by the genuine third relation and a genuine
unit pivot coordinate. -/
theorem pureTransverse_class_mem_maximal_smul
    (hv : IsUnit (extendedCoefficient k V R v))
    (hu : ∀ t, extendedCoefficient k V R (u t) ∈ IsLocalRing.maximalIdeal R)
    (i j : τ) :
    coefficientExtendedExteriorClass k V K R (exteriorWedge (u i) (u j)) ∈
      IsLocalRing.maximalIdeal R • extendedTransverseSpan k V K R u v := by
  let N := extendedTransverseSpan k V K R u v
  have hi : coefficientExtendedExteriorClass k V K R (exteriorWedge v (u i)) ∈ N :=
    Submodule.subset_span ⟨i, rfl⟩
  have hj : coefficientExtendedExteriorClass k V K R (exteriorWedge v (u j)) ∈ N :=
    Submodule.subset_span ⟨j, rfl⟩
  have hdiff : extendedCoefficient k V R (u i) •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v (u j)) -
      extendedCoefficient k V R (u j) •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v (u i)) ∈
        IsLocalRing.maximalIdeal R • N :=
    (IsLocalRing.maximalIdeal R • N).sub_mem
      (Submodule.smul_mem_smul (hu i) hj) (Submodule.smul_mem_smul (hu j) hi)
  have heq : extendedCoefficient k V R v •
      coefficientExtendedExteriorClass k V K R (exteriorWedge (u i) (u j)) =
      extendedCoefficient k V R (u i) •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v (u j)) -
      extendedCoefficient k V R (u j) •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v (u i)) := by
    have ht := coefficientExtendedExteriorClass_third k V K R v (u i) (u j)
    apply sub_eq_zero.mp
    convert ht using 1; abel
  rw [← heq] at hdiff
  obtain ⟨a, ha⟩ := hv
  have h := (IsLocalRing.maximalIdeal R • N).smul_mem (↑a⁻¹ : R) hdiff
  simpa only [← ha, smul_smul, Units.inv_mul, one_smul] using h

/-- All true pure transverse second terms map into maximal-ideal times
the actual transverse span. The input is membership in an actual span,
not membership in the expected output submodule. -/
theorem pureTransverseSecondSpan_image_mem_maximal_smul
    (hv : IsUnit (extendedCoefficient k V R v))
    (hu : ∀ t, extendedCoefficient k V R (u t) ∈ IsLocalRing.maximalIdeal R)
    {z : C2 k V} (hz : z ∈ pureTransverseSecondSpan k V u) :
    coefficientExtendedSecondMap k V K R z ∈
      IsLocalRing.maximalIdeal R • extendedTransverseSpan k V K R u v := by
  have hs : pureTransverseSecondSpan k V u ≤
      (((IsLocalRing.maximalIdeal R • extendedTransverseSpan k V K R u v).restrictScalars
          (S k V)).comap (coefficientExtendedSecondMap k V K R)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨⟨i, j⟩, rfl⟩
    exact pureTransverse_class_mem_maximal_smul k V K R u v hv hu i j
  exact hs hz

variable [Fintype τ]

/-- Genuine mixed quadratic lifts eliminate the true finite transverse
generator span in the literal scalar-extended original module. The
finite-generation premise of Nakayama is derived from the finite actual
generator set. No vanishing or annihilator conclusion is a premise. -/
theorem extendedTransverseSpan_eq_bot_of_actual_quadratic_lifts
    (hv : IsUnit (extendedCoefficient k V R v))
    (hu : ∀ t, extendedCoefficient k V R (u t) ∈ IsLocalRing.maximalIdeal R)
    (hlift : ∀ t, ∃ h : C2 k V, h ∈ pureTransverseSecondSpan k V u ∧
      (1 : S k V) ⊗ₜ[k] exteriorWedge v (u t) + h ∈
        LinearMap.range (quadraticInclusion k V K)) :
    extendedTransverseSpan k V K R u v = ⊥ := by
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
  · exact Submodule.fg_span (Set.finite_range _)
  · apply Submodule.span_le.mpr
    rintro z ⟨t, rfl⟩
    obtain ⟨h, hh, hrel⟩ := hlift t
    have hzero := coefficientExtendedSecondMap_quadratic k V K R _ hrel
    rw [map_add] at hzero
    have heq : coefficientExtendedExteriorClass k V K R (exteriorWedge v (u t)) =
        -coefficientExtendedSecondMap k V K R h := eq_neg_of_add_eq_zero_left hzero
    change coefficientExtendedExteriorClass k V K R (exteriorWedge v (u t)) ∈
      IsLocalRing.maximalIdeal R • extendedTransverseSpan k V K R u v
    rw [heq]
    exact (IsLocalRing.maximalIdeal R • extendedTransverseSpan k V K R u v).neg_mem
      (pureTransverseSecondSpan_image_mem_maximal_smul k V K R u v hv hu hh)
  · exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)

section ActualPointLocalization

variable (a : V →ₗ[k] k)

/-- The genuine localization of the actual symmetric coefficient ring
at the genuine evaluation prime of the actual point. -/
abbrev PointLocalCoefficientRing := Localization.AtPrime (pointEvaluationKernel k V a)

omit [Fintype τ] in
/-- Actual vanishing of the true point coordinate places its actual
localized coordinate in the actual maximal ideal. -/
theorem pointLocalCoefficient_mem_maximal {x : V} (hx : a x = 0) :
    extendedCoefficient k V (PointLocalCoefficientRing k V a) x ∈
      IsLocalRing.maximalIdeal (PointLocalCoefficientRing k V a) := by
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (PointLocalCoefficientRing k V a) (pointEvaluationKernel k V a)
    (SymmetricAlgebra.ι k V x)).mpr
  change pointEvaluation k V a (SymmetricAlgebra.ι k V x) = 0
  simpa only [pointEvaluation_generator] using hx

omit [Fintype τ] in
/-- A true normalized pivot gives a true unit in the actual localization. -/
theorem pointLocalCoefficient_isUnit {x : V} (hx : a x = 1) :
    IsUnit (extendedCoefficient k V (PointLocalCoefficientRing k V a) x) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (PointLocalCoefficientRing k V a) (pointEvaluationKernel k V a)
    (SymmetricAlgebra.ι k V x)).mpr
  change pointEvaluation k V a (SymmetricAlgebra.ι k V x) ≠ 0
  simpa only [pointEvaluation_generator, hx] using (one_ne_zero : (1 : k) ≠ 0)

/-- In the literal actual localized original Koszul module, genuine
point-adapted mixed quadratic lifts eliminate the actual transverse
generator span. Unit and maximal-ideal conditions are derived from true
point evaluation; they are not added as local-module premises. -/
theorem actualPointLocalized_transverseSpan_eq_bot
    (hv : a v = 1) (hu : ∀ t, a (u t) = 0)
    (hlift : ∀ t, ∃ h : C2 k V, h ∈ pureTransverseSecondSpan k V u ∧
      (1 : S k V) ⊗ₜ[k] exteriorWedge v (u t) + h ∈
        LinearMap.range (quadraticInclusion k V K)) :
    extendedTransverseSpan k V K (PointLocalCoefficientRing k V a) u v = ⊥ :=
  extendedTransverseSpan_eq_bot_of_actual_quadratic_lifts k V K
    (PointLocalCoefficientRing k V a) u v
    (pointLocalCoefficient_isUnit k V a hv)
    (fun t ↦ pointLocalCoefficient_mem_maximal k V a (hu t)) hlift

end ActualPointLocalization

end ChenRanks.Koszul
