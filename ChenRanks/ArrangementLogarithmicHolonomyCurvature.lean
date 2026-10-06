import ChenRanks.ExteriorAnnihilatorCanonicalTensor
import ChenRanks.QuadraticHolonomyGeneratorBracket
import ChenRanks.ArrangementSmoothQuadraticRelations

/-!
# Actual closed logarithmic coefficients have zero actual holonomy curvature

The source Lie algebra is the native quadratic holonomy quotient on the
dual of the original label space, with the actual determinant annihilator
of the actual original rational quadratic kernel. Its generators and
bracket are the actual native quotient maps.

The connection is a genuine finite sum in the literal tensor product of
the actual smooth coefficient exterior algebra and that Lie algebra.
The curvature is its genuine oriented-basis wedge/bracket sum. Native
closedness of the original normalized logarithms proves the derivative
term zero, while actual smooth relation killing and actual native Lie
relation killing prove the curvature term zero. Neither condition is
assumed. No local parallel solution, monodromy, Malcev comparison, or
formality conclusion is asserted here.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.AffineArrangement

open LieComparison OpenSmoothFunctions OpenSmoothExterior

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance actualCurvatureCoefficientCommRing :
    CommRing (SmoothFunction A.actualSmoothComplementOpen) :=
  inferInstanceAs (CommRing ↥(algebra A.actualSmoothComplementOpen))

local instance actualCurvatureTensorRing : Ring A.ActualSmoothCoefficientExterior :=
  Algebra.TensorProduct.instRing (R := ℂ)
    (A := SmoothFunction A.actualSmoothComplementOpen)
    (B := ConstantExterior (Fin d × Fin 2))

local instance actualCurvatureTensorModule : Module ℂ A.ActualSmoothCoefficientExterior :=
  inferInstanceAs (Module ℂ
    (SmoothFunction A.actualSmoothComplementOpen ⊗[ℂ] ConstantExterior (Fin d × Fin 2)))

/-- A genuine finite native basis of the original label space. -/
def actualLogHolonomyLabelBasis (_A : AffineArrangement d ι) :
    Module.Basis (Fin (Module.finrank ℂ (ι → ℂ))) ℂ (ι → ℂ) :=
  Module.finBasis ℂ (ι → ℂ)

/-- The native original quadratic holonomy Lie algebra, with the genuine
dual determinant annihilator as its relation subspace. -/
abbrev ActualLogarithmicHolonomyLie :=
  QuadraticHolonomyLie ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

/-- Original dual vectors map to actual native quotient generators. -/
def actualLogHolonomyGeneratorMap :
    Module.Dual ℂ (ι → ℂ) →ₗ[ℂ] A.ActualLogarithmicHolonomyLie :=
  quadraticHolonomyGenerators ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

/-- Original dual exterior vectors map to their actual native brackets. -/
def actualLogHolonomyBracketMap :
    (⋀[ℂ]^2 (Module.Dual ℂ (ι → ℂ))) →ₗ[ℂ] A.ActualLogarithmicHolonomyLie :=
  quadraticHolonomyGeneratorBracket ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

/-- The actual finite logarithmic connection tensor. -/
def actualSmoothLogHolonomyConnection :
    A.ActualSmoothCoefficientExterior ⊗[ℂ] A.ActualLogarithmicHolonomyLie :=
  ∑ i, A.actualNormalizedSmoothExteriorGeneratorMap (A.actualLogHolonomyLabelBasis i) ⊗ₜ[ℂ]
    A.actualLogHolonomyGeneratorMap (A.actualLogHolonomyLabelBasis.coord i)

/-- The true oriented wedge/bracket curvature of those same original
connection coefficients, indexed by the actual ordered native basis. -/
def actualSmoothLogHolonomyCurvature :
    A.ActualSmoothCoefficientExterior ⊗[ℂ] A.ActualLogarithmicHolonomyLie :=
  ∑ s : Set.powersetCard (Fin (Module.finrank ℂ (ι → ℂ))) 2,
    (A.actualNormalizedSmoothExteriorGeneratorMap
      (A.actualLogHolonomyLabelBasis (Set.powersetCard.ofFinEmbEquiv.symm s 0)) *
      A.actualNormalizedSmoothExteriorGeneratorMap
        (A.actualLogHolonomyLabelBasis (Set.powersetCard.ofFinEmbEquiv.symm s 1))) ⊗ₜ[ℂ]
      ⁅A.actualLogHolonomyGeneratorMap
          (A.actualLogHolonomyLabelBasis.coord (Set.powersetCard.ofFinEmbEquiv.symm s 0)),
        A.actualLogHolonomyGeneratorMap
          (A.actualLogHolonomyLabelBasis.coord (Set.powersetCard.ofFinEmbEquiv.symm s 1))⁆

/-- The derivative term of the same actual connection vanishes because
the actual original normalized logarithms are closed. -/
theorem actualSmoothLogHolonomyConnection_differential_eq_zero :
    TensorProduct.map A.actualSmoothCoefficientExteriorDifferential
      (LinearMap.id : A.ActualLogarithmicHolonomyLie →ₗ[ℂ] A.ActualLogarithmicHolonomyLie)
      A.actualSmoothLogHolonomyConnection = 0 := by
  unfold actualSmoothLogHolonomyConnection
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [TensorProduct.map_tmul, actualNormalizedSmoothExteriorGeneratorMap_closed,
    TensorProduct.zero_tmul]

private theorem exteriorMultiTwo_eq_wedge {E : Type*} [AddCommGroup E] [Module ℂ E]
    (v : Fin 2 → E) :
    exteriorPower.ιMulti ℂ 2 v = exteriorWedge (v 0) (v 1) := by
  change exteriorPower.ιMulti ℂ 2 v = exteriorPower.ιMulti ℂ 2 ![v 0, v 1]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The actual original quadratic relations and actual native quotient
relations force the actual curvature tensor to vanish. -/
theorem actualSmoothLogHolonomyCurvature_eq_zero :
    A.actualSmoothLogHolonomyCurvature = 0 := by
  have hβ : Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel ≤
      LinearMap.ker A.actualLogHolonomyBracketMap :=
    quadraticHolonomyRelation_le_generatorBracket_ker ℂ (Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
  have h := sum_exterior_basis_tmul_dual_eq_zero_of_annihilator
    A.actualLogHolonomyLabelBasis A.rationalQuadraticKernel
    A.actualNormalizedSmoothLogQuadraticMap A.actualLogHolonomyBracketMap
    A.rationalQuadraticKernel_le_actualNormalizedSmoothLogQuadraticMap_ker hβ
  unfold actualSmoothLogHolonomyCurvature
  convert h using 1
  apply Finset.sum_congr rfl
  intro s _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorMultiTwo_eq_wedge, actualNormalizedSmoothLogQuadraticMap_wedge,
    exteriorPower.ιMulti_family, exteriorMultiTwo_eq_wedge]
  change _ = _ ⊗ₜ[ℂ]
    quadraticHolonomyGeneratorBracket ℂ (Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) _
  rw [quadraticHolonomyGeneratorBracket_wedge]
  rfl

end ChenRanks.AffineArrangement
