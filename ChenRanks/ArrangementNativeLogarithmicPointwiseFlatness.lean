import ChenRanks.ArrangementSmoothExteriorTwoEvaluation

/-!
# The actual logarithmic tangent values commute in the actual holonomy algebra

At the actual complement point each original tangent vector produces a
genuine functional on the original label space. The genuine two-vector
evaluation of the original smooth exterior product is its determinant
pairing. The proved original quadratic relation killing therefore places
the exterior product of the two actual tangent functionals in the actual
determinant annihilator. The original native holonomy relations kill this
specific exterior product, proving the actual pointwise bracket zero.

No pointwise flatness, logarithmic relation-killing, exterior pairing, or
selected model is an input. A further actual Lie morphism to a finite
truncation preserves this proved bracket identity.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance nativeLogFlatLabelDecidableEq : DecidableEq ι := Classical.decEq ι

local instance nativeLogFlatActualTensorRing : Ring A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.instRing (R := ℂ)
    (A := OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen)
    (B := OpenSmoothExterior.ConstantExterior (Fin d × Fin 2))

local instance nativeLogFlatActualTensorNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring A.ActualSmoothCoefficientExterior :=
  (nativeLogFlatActualTensorRing A).toSemiring.toNonAssocSemiring.toNonUnitalNonAssocSemiring

local instance nativeLogFlatActualTensorModule : Module ℂ A.ActualSmoothCoefficientExterior :=
  inferInstanceAs (Module ℂ
    (OpenSmoothFunctions.SmoothFunction A.actualSmoothComplementOpen ⊗[ℂ]
      OpenSmoothExterior.ConstantExterior (Fin d × Fin 2)))

/-- Actual normalized logarithmic tangent evaluation, as an original
complex-linear functional on the entire original label space. -/
def actualNormalizedNativeLogTangentFunctional
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ) :
    Module.Dual ℂ (ι → ℂ) :=
  ∑ H : ι, (LinearMap.proj H).smulRight (A.actualNormalizedNativeLogValue H x u)

@[simp] theorem actualNormalizedNativeLogTangentFunctional_apply
    (x : A.actualSmoothComplementOpen) (u : Fin d → ℂ) (a : ι → ℂ) :
    A.actualNormalizedNativeLogTangentFunctional x u a =
      ∑ H : ι, a H * A.actualNormalizedNativeLogValue H x u := by
  simp [actualNormalizedNativeLogTangentFunctional, smul_eq_mul]

/-- The genuine actual coefficient-exterior product has the determinant
of the actual original tangent functionals on arbitrary label vectors. -/
theorem actualSmoothExteriorTwoEvaluation_generatorMaps
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) (a b : ι → ℂ) :
    A.actualSmoothExteriorTwoEvaluation x u v
      (A.actualNormalizedSmoothExteriorGeneratorMap a *
        A.actualNormalizedSmoothExteriorGeneratorMap b) =
      A.actualNormalizedNativeLogTangentFunctional x u a *
        A.actualNormalizedNativeLogTangentFunctional x v b -
      A.actualNormalizedNativeLogTangentFunctional x v a *
        A.actualNormalizedNativeLogTangentFunctional x u b := by
  rw [actualNormalizedSmoothExteriorGeneratorMap_apply,
    actualNormalizedSmoothExteriorGeneratorMap_apply,
    actualNormalizedNativeLogTangentFunctional_apply,
    actualNormalizedNativeLogTangentFunctional_apply,
    actualNormalizedNativeLogTangentFunctional_apply,
    actualNormalizedNativeLogTangentFunctional_apply]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, actualSmoothExteriorTwoEvaluation_normalized_logarithms,
    smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.sum_congr rfl
  intro K _
  ring

private theorem exteriorTwo_eq_wedge {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a : Fin 2 → E) :
    exteriorPower.ιMulti ℂ 2 a = exteriorWedge (a 0) (a 1) := by
  change exteriorPower.ιMulti ℂ 2 a = exteriorPower.ιMulti ℂ 2 ![a 0, a 1]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The genuine whole degree-two evaluation is the genuine native
determinant functional, proved on the actual exterior generators. -/
theorem actualNormalizedLogQuadratic_twoEvaluation_eq_pairing
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    (A.actualSmoothExteriorTwoEvaluation x u v).comp A.actualNormalizedSmoothLogQuadraticMap =
      exteriorPower.pairingDual ℂ (ι → ℂ) 2
        (exteriorWedge (A.actualNormalizedNativeLogTangentFunctional x u)
          (A.actualNormalizedNativeLogTangentFunctional x v)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change A.actualSmoothExteriorTwoEvaluation x u v
      (A.actualNormalizedSmoothLogQuadraticMap (exteriorPower.ιMulti ℂ 2 a)) = _
  rw [exteriorTwo_eq_wedge, actualNormalizedSmoothLogQuadraticMap_wedge,
    actualSmoothExteriorTwoEvaluation_generatorMaps]
  change _ = exteriorPower.pairingDual ℂ (ι → ℂ) 2
    (exteriorPower.ιMulti ℂ 2
      ![A.actualNormalizedNativeLogTangentFunctional x u,
        A.actualNormalizedNativeLogTangentFunctional x v])
    (exteriorPower.ιMulti ℂ 2 a)
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  simp [Matrix.det_fin_two, Matrix.of_apply]

/-- The two actual tangent values satisfy the genuine original
holonomy relation, because all actual original quadratic forms vanish. -/
theorem actualNormalizedNativeLogTangentFunctional_wedge_mem_annihilator
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    exteriorWedge (A.actualNormalizedNativeLogTangentFunctional x u)
      (A.actualNormalizedNativeLogTangentFunctional x v) ∈
      Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel := by
  rw [Koszul.mem_exteriorAnnihilator, Submodule.mem_dualAnnihilator]
  intro w hw
  rw [← actualNormalizedLogQuadratic_twoEvaluation_eq_pairing]
  change A.actualSmoothExteriorTwoEvaluation x u v
    (A.actualNormalizedSmoothLogQuadraticMap w) = 0
  rw [show A.actualNormalizedSmoothLogQuadraticMap w = 0 from
    A.rationalQuadraticKernel_le_actualNormalizedSmoothLogQuadraticMap_ker hw, map_zero]

/-- The actual normalized logarithmic tangent values have zero bracket
in the actual original native quadratic holonomy Lie algebra. -/
theorem actualNormalizedNativeLogTangent_holonomy_bracket_eq_zero
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    ⁅A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x u),
      A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x v)⁆ = 0 := by
  have h := quadraticHolonomyGeneratorBracket_eq_zero_of_mem ℂ
    (Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
    (exteriorWedge (A.actualNormalizedNativeLogTangentFunctional x u)
      (A.actualNormalizedNativeLogTangentFunctional x v))
    (A.actualNormalizedNativeLogTangentFunctional_wedge_mem_annihilator x u v)
  simpa only [quadraticHolonomyGeneratorBracket_wedge,
    actualLogHolonomyGeneratorMap] using h

/-- Every actual native Lie morphism preserves the already proved actual
logarithmic bracket identity; it does not supply pointwise flatness. -/
theorem actualNormalizedNativeLogTangent_map_bracket_eq_zero
    {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (f : A.ActualLogarithmicHolonomyLie →ₗ⁅ℂ⁆ L)
    (x : A.actualSmoothComplementOpen) (u v : Fin d → ℂ) :
    ⁅f (A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x u)),
      f (A.actualLogHolonomyGeneratorMap (A.actualNormalizedNativeLogTangentFunctional x v))⁆ = 0 := by
  rw [← f.map_lie, actualNormalizedNativeLogTangent_holonomy_bracket_eq_zero, map_zero]

end ChenRanks.AffineArrangement
