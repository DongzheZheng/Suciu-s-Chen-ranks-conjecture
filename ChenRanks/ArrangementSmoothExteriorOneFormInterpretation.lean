import ChenRanks.ArrangementSmoothExteriorLogarithms
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual degree-one interpretation as native smooth alternating forms

The actual real basis gives real continuous-linear coordinate functions.
An original constant covector is interpreted by their genuine finite
complex linear combination.  Actual smooth coefficients multiply this
native one-form pointwise, and true bilinearity constructs a map on the
literal coefficient tensor product.  On the original logarithmic tensor
this map is proved to be the original native smooth logarithmic one-form.
Only the degree-one interpretation is claimed here; higher-degree wedge
and differential compatibility and de Rham comparisons remain separate.
-/

noncomputable section


open scoped TensorProduct Topology

namespace ChenRanks

local instance actualBasisCovectorRealComplexScalarTower (d : ℕ) :
    IsScalarTower ℝ ℂ ((Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℂ) where
  smul_assoc a c ω := by
    ext v
    exact smul_assoc a c (ω v)

/-- Actual real continuous coordinate maps associated to the constructed
original real basis. -/
def actualRealBasisCoordinateCLM (d : ℕ) (i : Fin d × Fin 2) :
    (Fin d → ℂ) →L[ℝ] ℝ :=
  (complexAffineRealBasis d).coord i |>.toContinuousLinearMap

/-- True real-linear evaluation of an original constant complex covector. -/
def actualRealBasisCovectorCLM (d : ℕ) (α : (Fin d × Fin 2) → ℂ) :
    (Fin d → ℂ) →L[ℝ] ℂ :=
  ∑ i : Fin d × Fin 2, α i • (Complex.ofRealCLM.comp (actualRealBasisCoordinateCLM d i))

theorem actualRealBasisCovectorCLM_apply
    (d : ℕ) (α : (Fin d × Fin 2) → ℂ) (v : Fin d → ℂ) :
    actualRealBasisCovectorCLM d α v =
      ∑ i : Fin d × Fin 2, α i * ((complexAffineRealBasis d).repr v i : ℂ) := by
  simp [actualRealBasisCovectorCLM, actualRealBasisCoordinateCLM,
    Module.Basis.coord, smul_eq_mul]

/-- The actual native one-form associated to the actual covector. -/
def actualRealBasisCovectorOneForm (d : ℕ) (α : (Fin d × Fin 2) → ℂ) :
    (Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (Fin d → ℂ) ℂ 0
    (actualRealBasisCovectorCLM d α)

namespace AffineArrangement

open OpenSmoothFunctions OpenSmoothForms OpenSmoothExterior

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Actual basis evaluation recovers the original normal, by the genuine
native basis reconstruction of each original tangent vector. -/
theorem actualRealBasisCovectorCLM_original_normal (H : ι) :
    actualRealBasisCovectorCLM d (A.actualSmoothExteriorNormal H) =
      A.actualNormalRealCLM H := by
  apply ContinuousLinearMap.ext
  intro v
  rw [actualRealBasisCovectorCLM_apply]
  have hb := congrArg (A.actualNormalRealCLM H) ((complexAffineRealBasis d).sum_repr v)
  simp only [map_sum, map_smul, RCLike.real_smul_eq_coe_mul] at hb
  simpa only [actualSmoothExteriorNormal, actualNormalRealCLM_apply, mul_comm] using hb

theorem actualRealBasisCovectorOneForm_original_normal (H : ι) :
    actualRealBasisCovectorOneForm d (A.actualSmoothExteriorNormal H) =
      A.actualNormalRealOneForm H := by
  unfold actualRealBasisCovectorOneForm actualNormalRealOneForm
  rw [actualRealBasisCovectorCLM_original_normal]

/-- A true smooth coefficient multiplying the actual constant native
one-form.  Smoothness is proved on the actual original open complement. -/
def actualCoefficientCovectorOneForm
    (f : SmoothFunction A.actualSmoothComplementOpen)
    (α : (Fin d × Fin 2) → ℂ) :
    SmoothForm A.actualSmoothComplementOpen 1 := by
  refine ⟨fun x => f x • actualRealBasisCovectorOneForm d α, ?_⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (OpenSmoothForms.zeroExtension A.actualSmoothComplementOpen 1
      (fun x => f x • actualRealBasisCovectorOneForm d α)) A.actualSmoothComplementOpen
  have hs : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => OpenSmoothFunctions.zeroExtension A.actualSmoothComplementOpen f.val x •
        actualRealBasisCovectorOneForm d α) A.actualSmoothComplementOpen :=
    (OpenSmoothFunctions.smooth_zeroExtension A.actualSmoothComplementOpen f).smul
      contDiff_const.contDiffOn
  apply hs.congr
  intro x hx
  rw [OpenSmoothForms.zeroExtension_apply_mem A.actualSmoothComplementOpen 1 _ x hx,
    OpenSmoothFunctions.zeroExtension_apply_mem A.actualSmoothComplementOpen f.val x hx]

/-- Actual bilinear coefficient/covector evaluation on native smooth
one-forms; the module actions are the original complex pointwise ones. -/
def actualCoefficientCovectorOneFormBilinear :
    SmoothFunction A.actualSmoothComplementOpen →ₗ[ℂ]
      (((Fin d × Fin 2) → ℂ) →ₗ[ℂ] SmoothForm A.actualSmoothComplementOpen 1) where
  toFun f :=
    { toFun := A.actualCoefficientCovectorOneForm f
      map_add' α β := by
        apply Subtype.ext
        funext x
        ext v
        simp [actualCoefficientCovectorOneForm, actualRealBasisCovectorOneForm,
          actualRealBasisCovectorCLM, add_smul, Finset.sum_add_distrib, mul_add]
      map_smul' c α := by
        apply Subtype.ext
        funext x
        ext v
        simp [actualCoefficientCovectorOneForm, actualRealBasisCovectorOneForm,
          actualRealBasisCovectorCLM, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }
  map_add' f g := by
    apply LinearMap.ext
    intro α
    apply Subtype.ext
    funext x
    ext v
    simp [actualCoefficientCovectorOneForm, add_mul]
  map_smul' c f := by
    apply LinearMap.ext
    intro α
    apply Subtype.ext
    funext x
    ext v
    simp [actualCoefficientCovectorOneForm, smul_smul]

/-- Genuine native tensor evaluation into the original native smooth
one-form object. -/
def actualCoefficientOneFormTensorMap :
    (SmoothFunction A.actualSmoothComplementOpen ⊗[ℂ] ((Fin d × Fin 2) → ℂ)) →ₗ[ℂ]
      SmoothForm A.actualSmoothComplementOpen 1 :=
  TensorProduct.lift A.actualCoefficientCovectorOneFormBilinear

/-- First-degree interpretation uses the native exterior generator
projection, not an assumed exterior/native-form identification. -/
def actualSmoothExteriorOneFormInterpretation :
    A.ActualSmoothCoefficientExterior →ₗ[ℂ] SmoothForm A.actualSmoothComplementOpen 1 :=
  A.actualCoefficientOneFormTensorMap.comp
    (TensorProduct.map (LinearMap.id : SmoothFunction A.actualSmoothComplementOpen →ₗ[ℂ] _)
      (ExteriorAlgebra.ιInv :
        OpenSmoothExterior.ConstantExterior (Fin d × Fin 2) →ₗ[ℂ] ((Fin d × Fin 2) → ℂ)))

/-- On the actual original logarithm, the actual tensor interpretation is
the same original native smooth logarithmic one-form. -/
theorem actualSmoothExteriorOneFormInterpretation_logarithm (H : ι) :
    A.actualSmoothExteriorOneFormInterpretation (A.actualSmoothExteriorLogarithm H) =
      A.actualSmoothLogarithmicForm H := by
  have hι : (ExteriorAlgebra.ιInv : OpenSmoothExterior.ConstantExterior (Fin d × Fin 2) →ₗ[ℂ] _)
      (ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H)) = A.actualSmoothExteriorNormal H :=
    ExteriorAlgebra.ι_leftInverse _
  simp only [actualSmoothExteriorOneFormInterpretation, LinearMap.comp_apply,
    actualSmoothExteriorLogarithm, TensorProduct.map_tmul, LinearMap.id_apply, hι]
  change A.actualCoefficientCovectorOneForm (A.actualSmoothEquationInverse H)
    (A.actualSmoothExteriorNormal H) = A.actualSmoothLogarithmicForm H
  apply Subtype.ext
  funext x
  rw [show (A.actualCoefficientCovectorOneForm (A.actualSmoothEquationInverse H)
    (A.actualSmoothExteriorNormal H)).val x =
      A.actualSmoothEquationInverse H x •
        actualRealBasisCovectorOneForm d (A.actualSmoothExteriorNormal H) from rfl,
    actualRealBasisCovectorOneForm_original_normal]
  rfl

end AffineArrangement
end ChenRanks
