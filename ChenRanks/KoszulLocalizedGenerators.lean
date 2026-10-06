import ChenRanks.KoszulLocalizedTransverse

/-!
# Genuine pivot generators of the literal scalar-extended Koszul module

The module is still the literal scalar extension of the original quotient.
The true third relation and a true unit coefficient express all exterior
classes in the span of pivot classes. Actual exterior spanning and the
proved original second-term surjection then prove that this span is the
entire literal module. No original-module generation premise is used.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V))
variable (R : Type*) [CommRing R] [Algebra (S k V) R]

/-- The actual coefficient-module span of genuine pivot exterior classes. -/
def extendedPivotSpan (v : V) : Submodule R (CoefficientExtendedModule k V K R) :=
  Submodule.span R (Set.range fun w : V ↦
    coefficientExtendedExteriorClass k V K R (exteriorWedge v w))

/-- The actual third relation and a genuine unit pivot put every true
decomposable exterior class in the actual pivot span. -/
theorem exteriorClass_mem_extendedPivotSpan (v : V)
    (hv : IsUnit (extendedCoefficient k V R v)) (x y : V) :
    coefficientExtendedExteriorClass k V K R (exteriorWedge x y) ∈
      extendedPivotSpan k V K R v := by
  let N := extendedPivotSpan k V K R v
  have hx : coefficientExtendedExteriorClass k V K R (exteriorWedge v x) ∈ N :=
    Submodule.subset_span ⟨x, rfl⟩
  have hy : coefficientExtendedExteriorClass k V K R (exteriorWedge v y) ∈ N :=
    Submodule.subset_span ⟨y, rfl⟩
  have hdiff : extendedCoefficient k V R x •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v y) -
      extendedCoefficient k V R y •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v x) ∈ N :=
    N.sub_mem (N.smul_mem _ hy) (N.smul_mem _ hx)
  have heq : extendedCoefficient k V R v •
      coefficientExtendedExteriorClass k V K R (exteriorWedge x y) =
      extendedCoefficient k V R x •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v y) -
      extendedCoefficient k V R y •
        coefficientExtendedExteriorClass k V K R (exteriorWedge v x) := by
    have ht := coefficientExtendedExteriorClass_third k V K R v x y
    apply sub_eq_zero.mp
    convert ht using 1; abel
  rw [← heq] at hdiff
  obtain ⟨a, ha⟩ := hv
  have h := N.smul_mem (↑a⁻¹ : R) hdiff
  simpa only [← ha, smul_smul, Units.inv_mul, one_smul] using h

/-- Actual decomposable spanning gives pivot-span membership for every
actual exterior class, including nondecomposable ones. -/
theorem anyExteriorClass_mem_extendedPivotSpan (v : V)
    (hv : IsUnit (extendedCoefficient k V R v)) (w : ⋀[k]^2 V) :
    coefficientExtendedExteriorClass k V K R w ∈ extendedPivotSpan k V K R v := by
  let N := extendedPivotSpan k V K R v
  let L : Submodule (S k V) (C2 k V) :=
    (N.restrictScalars (S k V)).comap (coefficientExtendedSecondMap k V K R)
  have hspan : (⊤ : Submodule k (⋀[k]^2 V)) ≤
      (L.restrictScalars k).comap (TensorProduct.mk k (S k V) (⋀[k]^2 V) 1) := by
    rw [← exteriorWedge_span (k := k) (E := V)]
    apply Submodule.span_le.mpr
    rintro z ⟨x, y, rfl⟩
    exact exteriorClass_mem_extendedPivotSpan k V K R v hv x y
  exact hspan (show w ∈ (⊤ : Submodule k (⋀[k]^2 V)) from trivial)

/-- Every genuine second tensor term maps to the actual pivot span. -/
theorem secondMap_mem_extendedPivotSpan (v : V)
    (hv : IsUnit (extendedCoefficient k V R v)) (z : C2 k V) :
    coefficientExtendedSecondMap k V K R z ∈ extendedPivotSpan k V K R v := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact (extendedPivotSpan k V K R v).zero_mem
  | add z t hz ht =>
      rw [map_add]
      exact (extendedPivotSpan k V K R v).add_mem hz ht
  | tmul s w =>
      have hs : s ⊗ₜ[k] w = s • ((1 : S k V) ⊗ₜ[k] w) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, coefficientExtendedSecondMap_smul]
      exact (extendedPivotSpan k V K R v).smul_mem _
        (anyExteriorClass_mem_extendedPivotSpan k V K R v hv w)

variable [FiniteDimensional k V] [CharZero k]

/-- Actual exterior spanning, tensor induction, and the proved original
second-term surjection show that the true pivot span is the entire
literal scalar-extended original module. -/
theorem extendedPivotSpan_eq_top (v : V)
    (hv : IsUnit (extendedCoefficient k V R v)) : extendedPivotSpan k V K R v = ⊤ := by
  apply top_unique
  intro z _
  induction z using TensorProduct.induction_on with
  | zero => exact (extendedPivotSpan k V K R v).zero_mem
  | add z t hz ht => exact (extendedPivotSpan k V K R v).add_mem (hz trivial) (ht trivial)
  | tmul r w =>
      obtain ⟨x, rfl⟩ := secondTensorToModule_surjective k V K w
      have h := (extendedPivotSpan k V K R v).smul_mem r
        (secondMap_mem_extendedPivotSpan k V K R v hv x)
      change r • ((1 : R) ⊗ₜ[S k V] secondTensorToModule k V K x) ∈
        extendedPivotSpan k V K R v at h
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

end ChenRanks.Koszul
