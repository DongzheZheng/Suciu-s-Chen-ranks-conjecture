import ChenRanks.NativeExteriorTwoEvaluation
import ChenRanks.ArrangementSmoothExteriorOneFormInterpretation
import ChenRanks.ArrangementLogarithmicHolonomyCurvature

/-!
# Genuine pointwise two-vector evaluation of the actual logarithmic curvature

The actual real coordinate basis supplies actual complex-linear functionals
on the constant covector space. The original smooth coefficient is evaluated
at the original complement point. Genuine bilinearity combines these maps
on the literal coefficient tensor product. The value of a product of two
original logarithms is proved to be the determinant of their actual values
on the two original tangent vectors. Applying this genuine linear map to
the proved curvature tensor identity produces a pointwise identity in the
original native holonomy Lie algebra.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks

/-- An original real tangent vector evaluates actual constant complex
covectors complex-linearly, using the already constructed real basis. -/
def actualRealBasisTangentEvaluation (d : ℕ) (v : Fin d → ℂ) :
    ((Fin d × Fin 2) → ℂ) →ₗ[ℂ] ℂ where
  toFun α := actualRealBasisCovectorCLM d α v
  map_add' α β := by
    simp only [actualRealBasisCovectorCLM_apply, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' c α := by
    simp only [actualRealBasisCovectorCLM_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc, RingHom.id_apply]

@[simp] theorem actualRealBasisTangentEvaluation_apply
    (d : ℕ) (v : Fin d → ℂ) (α : (Fin d × Fin 2) → ℂ) :
    actualRealBasisTangentEvaluation d v α = actualRealBasisCovectorCLM d α v := rfl

namespace AffineArrangement

open OpenSmoothFunctions OpenSmoothExterior LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance smoothTwoEvaluationCoefficientCommRing :
    CommRing (SmoothFunction A.actualSmoothComplementOpen) :=
  inferInstanceAs (CommRing ↥(algebra A.actualSmoothComplementOpen))

local instance smoothTwoEvaluationActualTensorRing : Ring A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.instRing (R := ℂ)
    (A := SmoothFunction A.actualSmoothComplementOpen)
    (B := ConstantExterior (Fin d × Fin 2))

local instance smoothTwoEvaluationActualTensorModule :
    Module ℂ A.ActualSmoothCoefficientExterior :=
  inferInstanceAs (Module ℂ
    (SmoothFunction A.actualSmoothComplementOpen ⊗[ℂ]
      ConstantExterior (Fin d × Fin 2)))

/-- Original smooth-function evaluation and actual determinant evaluation
form a genuine bilinear map, with the original scalar actions. -/
def actualSmoothExteriorTwoEvaluationBilinear
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    SmoothFunction A.actualSmoothComplementOpen →ₗ[ℂ]
      (ConstantExterior (Fin d × Fin 2) →ₗ[ℂ] ℂ) where
  toFun f := f x • nativeExteriorTwoEvaluation ℂ ((Fin d × Fin 2) → ℂ)
    (actualRealBasisTangentEvaluation d u) (actualRealBasisTangentEvaluation d v)
  map_add' f g := by
    apply LinearMap.ext
    intro a
    change (f x + g x) * _ = f x * _ + g x * _
    exact add_mul _ _ _
  map_smul' c f := by
    apply LinearMap.ext
    intro a
    change (c * f x) * _ = c * (f x * _)
    exact mul_assoc _ _ _

/-- The actual linear functional on the literal actual coefficient
exterior tensor product; it is constructed, rather than selected. -/
def actualSmoothExteriorTwoEvaluation
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    A.ActualSmoothCoefficientExterior →ₗ[ℂ] ℂ :=
  TensorProduct.lift (A.actualSmoothExteriorTwoEvaluationBilinear x u v)

@[simp] theorem actualSmoothExteriorTwoEvaluation_tmul
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ)
    (f : SmoothFunction A.actualSmoothComplementOpen)
    (a : ConstantExterior (Fin d × Fin 2)) :
    A.actualSmoothExteriorTwoEvaluation x u v (f ⊗ₜ[ℂ] a) =
      f x * nativeExteriorTwoEvaluation ℂ ((Fin d × Fin 2) → ℂ)
        (actualRealBasisTangentEvaluation d u) (actualRealBasisTangentEvaluation d v) a :=
  rfl

/-- Evaluation of the actual product of two original coefficient
generators is its actual determinant, including scalar coefficients. -/
theorem actualSmoothExteriorTwoEvaluation_generator_product
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ)
    (f g : SmoothFunction A.actualSmoothComplementOpen)
    (α β : (Fin d × Fin 2) → ℂ) :
    A.actualSmoothExteriorTwoEvaluation x u v
      ((f ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ α) *
        (g ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ β)) =
      f x * g x * (actualRealBasisCovectorCLM d α u *
        actualRealBasisCovectorCLM d β v -
        actualRealBasisCovectorCLM d α v * actualRealBasisCovectorCLM d β u) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, actualSmoothExteriorTwoEvaluation_tmul,
    nativeExteriorTwoEvaluation_generator_product]
  rfl

/-- Actual normalized logarithm evaluation on an original tangent vector. -/
def actualNormalizedNativeLogValue (H : ι) (x : A.actualSmoothComplementOpen)
    (u : Fin d → ℂ) : ℂ :=
  logarithmicPeriodConstant⁻¹ * (A.normal H x.val - A.offset H)⁻¹ * A.normal H u

/-- The actual coefficient-exterior product agrees with the actual
normalized native logarithm determinant. No form-interpretation premise. -/
theorem actualSmoothExteriorTwoEvaluation_normalized_logarithms
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) (H K : ι) :
    A.actualSmoothExteriorTwoEvaluation x u v
      (A.actualNormalizedSmoothExteriorLogarithm H *
        A.actualNormalizedSmoothExteriorLogarithm K) =
      A.actualNormalizedNativeLogValue H x u * A.actualNormalizedNativeLogValue K x v -
        A.actualNormalizedNativeLogValue H x v * A.actualNormalizedNativeLogValue K x u := by
  unfold actualNormalizedSmoothExteriorLogarithm actualSmoothExteriorLogarithm
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
    actualSmoothExteriorTwoEvaluation_generator_product,
    A.actualRealBasisCovectorCLM_original_normal H,
    A.actualRealBasisCovectorCLM_original_normal K]
  simp only [actualNormalRealCLM_apply]
  change logarithmicPeriodConstant⁻¹ *
    (logarithmicPeriodConstant⁻¹ *
      ((A.normal H x.val - A.offset H)⁻¹ * (A.normal K x.val - A.offset K)⁻¹ *
        (A.normal H u * A.normal K v - A.normal H v * A.normal K u))) = _
  unfold actualNormalizedNativeLogValue
  ring

/-- The same actual coefficient functional evaluates the literal
coefficient/holonomy tensor to the original holonomy Lie algebra. -/
def actualSmoothHolonomyTwoEvaluation
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    (A.ActualSmoothCoefficientExterior ⊗[ℂ] A.ActualLogarithmicHolonomyLie) →ₗ[ℂ]
      A.ActualLogarithmicHolonomyLie :=
  (TensorProduct.lid ℂ A.ActualLogarithmicHolonomyLie).toLinearMap.comp
    (TensorProduct.map (A.actualSmoothExteriorTwoEvaluation x u v) LinearMap.id)

@[simp] theorem actualSmoothHolonomyTwoEvaluation_tmul
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ)
    (a : A.ActualSmoothCoefficientExterior) (z : A.ActualLogarithmicHolonomyLie) :
    A.actualSmoothHolonomyTwoEvaluation x u v (a ⊗ₜ[ℂ] z) =
      A.actualSmoothExteriorTwoEvaluation x u v a • z := rfl

/-- The proved actual curvature identity yields a genuine pointwise
bracket identity at the original point and two original real vectors. -/
theorem actualSmoothHolonomyTwoEvaluation_curvature_eq_zero
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    (∑ s : Set.powersetCard (Fin (Module.finrank ℂ (ι → ℂ))) 2,
      A.actualSmoothExteriorTwoEvaluation x u v
        (A.actualNormalizedSmoothExteriorGeneratorMap
          (A.actualLogHolonomyLabelBasis (Set.powersetCard.ofFinEmbEquiv.symm s 0)) *
          A.actualNormalizedSmoothExteriorGeneratorMap
            (A.actualLogHolonomyLabelBasis (Set.powersetCard.ofFinEmbEquiv.symm s 1))) •
        ⁅A.actualLogHolonomyGeneratorMap
          (A.actualLogHolonomyLabelBasis.coord (Set.powersetCard.ofFinEmbEquiv.symm s 0)),
         A.actualLogHolonomyGeneratorMap
          (A.actualLogHolonomyLabelBasis.coord (Set.powersetCard.ofFinEmbEquiv.symm s 1))⁆) = 0 := by
  have h := congrArg (A.actualSmoothHolonomyTwoEvaluation x u v)
    A.actualSmoothLogHolonomyCurvature_eq_zero
  have hz : A.actualSmoothHolonomyTwoEvaluation x u v
      (0 : A.ActualSmoothCoefficientExterior ⊗[ℂ] A.ActualLogarithmicHolonomyLie) = 0 :=
    (A.actualSmoothHolonomyTwoEvaluation x u v).map_zero
  rw [hz] at h
  simpa only [actualSmoothLogHolonomyCurvature, map_sum,
    actualSmoothHolonomyTwoEvaluation_tmul] using h

end AffineArrangement
end ChenRanks
