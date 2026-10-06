import ChenRanks.ArrangementSmoothExteriorLogarithms
import ChenRanks.AffineQuadraticKernel

/-!
# Original quadratic relations are killed in the actual smooth exterior ring

The original affine polynomial relation is evaluated on the actual
complement.  Subtracting its value at zero derives the actual normal
relation, retaining all affine offsets.  Pointwise complex arithmetic
proves the reciprocal coefficient identity in the genuine smooth-function
ring.  These identities kill the actual parallel and triple generators;
the already proved actual rational-kernel spanning theorem then kills the
whole original quadratic kernel.  No relation-killing or cup comparison
condition is supplied.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.AffineArrangement

open OpenSmoothFunctions

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance smoothQuadraticRelationLabelDecidableEq : DecidableEq ι := Classical.decEq ι

local instance smoothQuadraticOriginalCoefficientCommRing :
    CommRing (SmoothFunction A.actualSmoothComplementOpen) :=
  inferInstanceAs (CommRing ↥(algebra A.actualSmoothComplementOpen))

local instance smoothQuadraticOriginalCoefficientModule :
    Module ℂ (SmoothFunction A.actualSmoothComplementOpen) :=
  inferInstanceAs (Module ℂ ↥(algebra A.actualSmoothComplementOpen))

local instance smoothQuadraticOriginalCoefficientMulAction :
    MulAction ℂ (SmoothFunction A.actualSmoothComplementOpen) :=
  (smoothQuadraticOriginalCoefficientModule A).toDistribMulAction.toMulAction

local instance smoothQuadraticOriginalTensorRing : Ring A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.instRing (R := ℂ)
    (A := SmoothFunction A.actualSmoothComplementOpen)
    (B := OpenSmoothExterior.ConstantExterior (Fin d × Fin 2))

local instance smoothQuadraticOriginalTensorSelfMulAction :
    MulAction A.ActualSmoothCoefficientExterior A.ActualSmoothCoefficientExterior :=
  @Monoid.toMulAction A.ActualSmoothCoefficientExterior
    (smoothQuadraticOriginalTensorRing A).toSemiring.toMonoidWithZero.toMonoid

local instance smoothQuadraticOriginalTensorSelfSMul :
    SMul A.ActualSmoothCoefficientExterior A.ActualSmoothCoefficientExterior :=
  (smoothQuadraticOriginalTensorSelfMulAction A).toSMul

local instance smoothQuadraticOriginalTensorModule : Module ℂ A.ActualSmoothCoefficientExterior :=
  inferInstanceAs (Module ℂ
    (SmoothFunction A.actualSmoothComplementOpen ⊗[ℂ]
      OpenSmoothExterior.ConstantExterior (Fin d × Fin 2)))

local instance smoothQuadraticOriginalTensorMulAction : MulAction ℂ A.ActualSmoothCoefficientExterior :=
  (smoothQuadraticOriginalTensorModule A).toDistribMulAction.toMulAction

local instance smoothQuadraticOriginalTensorScalarComm :
    SMulCommClass ℂ A.ActualSmoothCoefficientExterior A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.sMulCommClass_right (R := ℂ) (S := ℂ)
    (A := SmoothFunction A.actualSmoothComplementOpen)
    (B := OpenSmoothExterior.ConstantExterior (Fin d × Fin 2))

local instance smoothQuadraticOriginalTensorScalarTower :
    IsScalarTower ℂ A.ActualSmoothCoefficientExterior A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.isScalarTower_right (R := ℂ) (S := ℂ)
    (A := SmoothFunction A.actualSmoothComplementOpen)
    (B := OpenSmoothExterior.ConstantExterior (Fin d × Fin 2))

theorem actualAffineEquation_relation_of_polynomial_relation
    (H K L : ι) (a b : ℂ)
    (hpoly : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K)
    (x : Fin d → ℂ) :
    A.actualAffineEquationFunction L x =
      a * A.actualAffineEquationFunction H x + b * A.actualAffineEquationFunction K x := by
  have he := congrArg (MvPolynomial.eval x) hpoly
  simpa only [map_add, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    equationPolynomial_eval, actualAffineEquationFunction] using he

/-- Original normal dependence is derived by evaluating the original
affine relation both at the actual point and at zero. -/
theorem actualSmoothExteriorNormal_relation_of_polynomial_relation
    (H K L : ι) (a b : ℂ)
    (hpoly : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    A.actualSmoothExteriorNormal L =
      a • A.actualSmoothExteriorNormal H + b • A.actualSmoothExteriorNormal K := by
  funext i
  have hx := A.actualAffineEquation_relation_of_polynomial_relation
    H K L a b hpoly (complexAffineRealBasis d i)
  have h0 := A.actualAffineEquation_relation_of_polynomial_relation H K L a b hpoly 0
  simp only [actualAffineEquationFunction, map_zero, zero_sub] at hx h0
  change A.normal L (complexAffineRealBasis d i) =
    a * A.normal H (complexAffineRealBasis d i) + b * A.normal K (complexAffineRealBasis d i)
  linear_combination hx - h0

/-- A true reciprocal identity in the actual smooth coefficient ring,
proved pointwise using the original complement's nonzero equations. -/
theorem actualSmoothInverse_triple_coefficient_identity
    (H K L : ι) (a b : ℂ)
    (hpoly : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    -(a • (A.actualSmoothEquationInverse K * A.actualSmoothEquationInverse L)) -
      b • (A.actualSmoothEquationInverse H * A.actualSmoothEquationInverse L) +
        A.actualSmoothEquationInverse H * A.actualSmoothEquationInverse K = 0 := by
  apply Subtype.ext
  funext x
  change -(a * ((A.normal K x.val - A.offset K)⁻¹ *
      (A.normal L x.val - A.offset L)⁻¹)) -
    b * ((A.normal H x.val - A.offset H)⁻¹ * (A.normal L x.val - A.offset L)⁻¹) +
      (A.normal H x.val - A.offset H)⁻¹ * (A.normal K x.val - A.offset K)⁻¹ = 0
  have hH := sub_ne_zero.mpr (x.property H)
  have hK := sub_ne_zero.mpr (x.property K)
  have hL := sub_ne_zero.mpr (x.property L)
  have he := A.actualAffineEquation_relation_of_polynomial_relation H K L a b hpoly x.val
  change A.normal L x.val - A.offset L =
    a * (A.normal H x.val - A.offset H) + b * (A.normal K x.val - A.offset K) at he
  field_simp [hH, hK, hL]
  rw [he]
  ring

/-- Original parallel pairs vanish in the same actual coefficient ring. -/
theorem actualSmoothExteriorLogarithms_parallel_product_eq_zero
    (H K : ι) (c : ℂ) (hc : A.normal K = c • A.normal H) :
    A.actualSmoothExteriorLogarithm H * A.actualSmoothExteriorLogarithm K = 0 := by
  have hα : A.actualSmoothExteriorNormal K = c • A.actualSmoothExteriorNormal H := by
    funext i
    change A.normal K (complexAffineRealBasis d i) = c * A.normal H (complexAffineRealBasis d i)
    simpa only [LinearMap.smul_apply, smul_eq_mul] using
      DFunLike.congr_fun hc (complexAffineRealBasis d i)
  unfold actualSmoothExteriorLogarithm
  rw [Algebra.TensorProduct.tmul_mul_tmul, hα, map_smul,
    mul_smul_comm, ExteriorAlgebra.ι_sq_zero, smul_zero, TensorProduct.tmul_zero]

/-- Original affine triple boundaries vanish using the actual smooth
reciprocal coefficients and the actual original normal relation. -/
theorem actualSmoothExteriorLogarithms_triple_boundary_eq_zero
    (H K L : ι) (a b : ℂ)
    (hpoly : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    A.actualSmoothExteriorLogarithm K * A.actualSmoothExteriorLogarithm L -
      A.actualSmoothExteriorLogarithm H * A.actualSmoothExteriorLogarithm L +
        A.actualSmoothExteriorLogarithm H * A.actualSmoothExteriorLogarithm K = 0 := by
  have hα := A.actualSmoothExteriorNormal_relation_of_polynomial_relation H K L a b hpoly
  have hswap : ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal K) *
      ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H) =
      -(ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal H) *
        ExteriorAlgebra.ι ℂ (A.actualSmoothExteriorNormal K)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap
      (A.actualSmoothExteriorNormal K) (A.actualSmoothExteriorNormal H))
  unfold actualSmoothExteriorLogarithm
  simp only [Algebra.TensorProduct.tmul_mul_tmul, hα, map_add, map_smul,
    mul_add, mul_smul_comm, ExteriorAlgebra.ι_sq_zero, smul_zero, add_zero, zero_add,
    hswap, smul_neg, TensorProduct.tmul_neg, TensorProduct.tmul_smul]
  simp only [TensorProduct.smul_tmul', ← TensorProduct.neg_tmul,
    ← TensorProduct.sub_tmul, ← TensorProduct.add_tmul,
    A.actualSmoothInverse_triple_coefficient_identity H K L a b hpoly,
    TensorProduct.zero_tmul]

/-- The actual normalized map restricted to the genuine original degree
two submodule. -/
def actualNormalizedSmoothLogQuadraticMap :
    (⋀[ℂ]^2 (ι → ℂ)) →ₗ[ℂ] A.ActualSmoothCoefficientExterior :=
  A.actualNormalizedSmoothLogExteriorHom.toLinearMap.comp
    (⋀[ℂ]^2 (ι → ℂ)).subtype

theorem actualNormalizedSmoothLogQuadraticMap_wedge (x y : ι → ℂ) :
    A.actualNormalizedSmoothLogQuadraticMap (exteriorWedge (k := ℂ) x y) =
      A.actualNormalizedSmoothExteriorGeneratorMap x *
        A.actualNormalizedSmoothExteriorGeneratorMap y := by
  change A.actualNormalizedSmoothLogExteriorHom
    (exteriorWedge (k := ℂ) x y).val = _
  rw [exteriorWedge_coe, map_mul, actualNormalizedSmoothLogExteriorHom_iota,
    actualNormalizedSmoothLogExteriorHom_iota]

@[simp] theorem actualNormalizedSmoothExteriorGeneratorMap_basis (H : ι) :
    A.actualNormalizedSmoothExteriorGeneratorMap (Pi.single H 1) =
      A.actualNormalizedSmoothExteriorLogarithm H := by
  simp [actualNormalizedSmoothExteriorGeneratorMap_apply]

/-- The entire actual rational quadratic kernel is killed without any
model, relation-killing hypothesis, or prescribed topological kernel. -/
theorem rationalQuadraticKernel_le_actualNormalizedSmoothLogQuadraticMap_ker :
    A.rationalQuadraticKernel ≤ LinearMap.ker A.actualNormalizedSmoothLogQuadraticMap := by
  rw [A.rationalQuadraticKernel_eq_affineQuadraticEquationBoundarySpan]
  apply Submodule.span_le.mpr
  rintro z (hparallel | htriple)
  · obtain ⟨H, K, ⟨c, hc⟩, rfl⟩ := hparallel
    change A.actualNormalizedSmoothLogQuadraticMap
      (exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)) = 0
    rw [actualNormalizedSmoothLogQuadraticMap_wedge,
      actualNormalizedSmoothExteriorGeneratorMap_basis,
      actualNormalizedSmoothExteriorGeneratorMap_basis]
    simp only [actualNormalizedSmoothExteriorLogarithm, smul_mul_assoc, mul_smul_comm,
      A.actualSmoothExteriorLogarithms_parallel_product_eq_zero H K c hc, smul_zero]
  · obtain ⟨H, K, L, hspan, rfl⟩ := htriple
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
    change A.actualNormalizedSmoothLogQuadraticMap (tripleBoundary H K L) = 0
    rw [tripleBoundary, map_add, map_sub]
    simp only [actualNormalizedSmoothLogQuadraticMap_wedge,
      actualNormalizedSmoothExteriorGeneratorMap_basis,
      actualNormalizedSmoothExteriorLogarithm, smul_mul_assoc, mul_smul_comm,
      ← smul_sub, ← smul_add,
      A.actualSmoothExteriorLogarithms_triple_boundary_eq_zero H K L a b hab.symm,
      smul_zero]

end ChenRanks.AffineArrangement
