import ChenRanks.ArrangementObjects

/-!
# Actual central complement and its affine slice

For the original central arrangement, a chosen original hyperplane equation
gives a nonzero scale on the original complement. Dividing the original
point by this scale lies in the actual affine slice where that equation
equals one. Rescaling is the inverse, and the actual maps are continuous.

This proves the manuscript's topological product reduction on the genuine
slice, before choosing coordinates to express the slice as a lower-dimensional
affine arrangement and counting its hyperplanes.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The genuine affine slice complement inside the original complex
vector space, retaining every original hyperplane equation. -/
def CentralSliceComplement (i₀ : ι) :=
  {x : Fin d → ℂ // A.normal i₀ x = 1 ∧ ∀ i, A.normal i x ≠ 0}

instance centralSliceComplement_topologicalSpace (i₀ : ι) :
    TopologicalSpace (A.CentralSliceComplement i₀) := by
  unfold CentralSliceComplement
  infer_instance

variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)

include hcentral in
/-- Each actual central normal is nonzero on the original complement. -/
theorem normal_ne_zero_on_central_complement (x : A.Complement) (i : ι) :
    A.normal i x.val ≠ 0 := by
  simpa only [hcentral i] using x.property i

/-- The nonzero value of the actual chosen hyperplane equation, as an
actual complex unit. -/
def centralScale (x : A.Complement) : ℂˣ :=
  Units.mk0 (A.normal i₀ x.val) (A.normal_ne_zero_on_central_complement hcentral x i₀)

/-- Normalize the original point into the original affine slice. -/
def centralSlicePoint (x : A.Complement) : A.CentralSliceComplement i₀ :=
  ⟨(A.normal i₀ x.val)⁻¹ • x.val, by
    constructor
    · rw [map_smul, smul_eq_mul]
      exact inv_mul_cancel₀ (A.normal_ne_zero_on_central_complement hcentral x i₀)
    · intro i
      rw [map_smul, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero (A.normal_ne_zero_on_central_complement hcentral x i₀))
        (A.normal_ne_zero_on_central_complement hcentral x i)⟩

/-- Rescale the genuine slice point by an actual complex unit. -/
def centralRescale (x : A.CentralSliceComplement i₀ × ℂˣ) : A.Complement :=
  ⟨(x.2 : ℂ) • x.1.val, by
    intro i
    rw [map_smul, hcentral i, smul_eq_mul]
    exact mul_ne_zero x.2.ne_zero (x.1.property.2 i)⟩

/-- The original scale is continuous, including its actual inverse
coordinate in the native topology of units. -/
theorem centralScale_continuous : Continuous (A.centralScale hcentral i₀) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun x : A.Complement ↦ A.normal i₀ x.val) :=
    (A.normal i₀).continuous_of_finiteDimensional.comp continuous_subtype_val
  constructor
  · simpa only [centralScale, Units.val_mk0] using h
  · simpa only [centralScale, Units.val_inv_eq_inv_val, Units.val_mk0] using
      h.inv₀ (fun x ↦ A.normal_ne_zero_on_central_complement hcentral x i₀)

/-- The original normalization into the genuine slice is continuous. -/
theorem centralSlicePoint_continuous : Continuous (A.centralSlicePoint hcentral i₀) := by
  apply Continuous.subtype_mk
  exact (((A.normal i₀).continuous_of_finiteDimensional.comp continuous_subtype_val).inv₀
    (fun x ↦ A.normal_ne_zero_on_central_complement hcentral x i₀)).smul continuous_subtype_val

/-- The actual inverse rescaling map is continuous. -/
theorem centralRescale_continuous : Continuous (A.centralRescale hcentral i₀) := by
  apply Continuous.subtype_mk
  exact (Units.continuous_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)

/-- The actual central complement is homeomorphic to its original
affine slice complement times the actual nonzero complex scalars. -/
def centralComplementSliceHomeomorph :
    A.Complement ≃ₜ A.CentralSliceComplement i₀ × ℂˣ where
  toFun x := (A.centralSlicePoint hcentral i₀ x, A.centralScale hcentral i₀ x)
  invFun x := A.centralRescale hcentral i₀ x
  left_inv x := by
    apply Subtype.ext
    change A.normal i₀ x.val • ((A.normal i₀ x.val)⁻¹ • x.val) = x.val
    rw [← mul_smul, mul_inv_cancel₀
      (A.normal_ne_zero_on_central_complement hcentral x i₀), one_smul]
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change (A.normal i₀ ((x.2 : ℂ) • x.1.val))⁻¹ • ((x.2 : ℂ) • x.1.val) = x.1.val
      rw [map_smul, x.1.property.1, smul_eq_mul, mul_one,
        ← mul_smul, inv_mul_cancel₀ x.2.ne_zero, one_smul]
    · apply Units.ext
      change A.normal i₀ ((x.2 : ℂ) • x.1.val) = (x.2 : ℂ)
      rw [map_smul, x.1.property.1, smul_eq_mul, mul_one]
  continuous_toFun := (A.centralSlicePoint_continuous hcentral i₀).prodMk
    (A.centralScale_continuous hcentral i₀)
  continuous_invFun := A.centralRescale_continuous hcentral i₀

end ChenRanks.AffineArrangement
