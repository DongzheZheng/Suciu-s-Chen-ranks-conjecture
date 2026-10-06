import ChenRanks.HyperplaneTwoFormResidueRows
import ChenRanks.ExteriorCoordinateRowDecomposition

/-!
# Actual residue rows of every original quadratic-kernel element

The complementary projection at the original coordinate H is constructed
from that coordinate functional and its actual coordinate vector. Its
images have H-coordinate zero. Each such image has an actual regular
logarithmic lift in the same original hyperplane local ring: sum the
already constructed regular logarithms of all other original equations.

The genuine exterior-square span theorem then puts the complementary
quadratic image of every exterior vector in the actual regular-tensor
image. Thus a genuine tensor remainder is obtained as a conclusion, not
introduced as a regular-lift premise. The actual contraction decomposition
and the actual two-form residue give all pivot-restricted logarithmic
rows for every element of the original rational quadratic kernel.

This is the residue-row step of the quadratic-kernel reverse inclusion.
Identifying the kernel of these rows with the affine codimension-two
boundary blocks, and the comparison with singular cup products, remain
separate theorems.
-/

noncomputable section

open scoped TensorProduct BigOperators

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance hyperplaneQuadraticKernelRowsDecidableEq : DecidableEq ι := Classical.decEq ι

local instance hyperplaneKernelRows_commRing (H : ι) : CommRing (A.hyperplaneLocalRing H) :=
  A.hyperplaneLocalRing_commRing H

local instance hyperplaneKernelRows_commMonoid (H : ι) : CommMonoid (A.hyperplaneLocalRing H) :=
  (hyperplaneKernelRows_commRing A H).toCommMonoid

local instance hyperplaneKernelRows_selfAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) :=
  Algebra.id (A.hyperplaneLocalRing H)

local instance hyperplaneKernelRows_selfModule (H : ι) :
    Module (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) := Algebra.toModule

local instance hyperplaneKernelRows_selfSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) :=
  (hyperplaneKernelRows_selfAlgebra A H).toSMul

local instance hyperplaneKernelRows_residueAlgebra (H : ι) :
    Algebra (A.hyperplaneLocalRing H) (IsLocalRing.ResidueField (A.hyperplaneLocalRing H)) :=
  IsLocalRing.ResidueField.algebra (A.hyperplaneLocalRing H)
    (R₀ := A.hyperplaneLocalRing H)

local instance hyperplaneKernelRows_nativeLieRing (H : ι) :
    LieRing (A.hyperplaneLocalRing H) := LieRing.ofAssociativeRing

local instance hyperplaneKernelRows_localScalarComm (H : ι) :
    SMulCommClass ℂ (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H) where
  smul_comm c a b := by
    simp only [Algebra.smul_def]
    change algebraMap ℂ (A.hyperplaneLocalRing H) c * (a * b) =
      a * (algebraMap ℂ (A.hyperplaneLocalRing H) c * b)
    exact @mul_left_comm _ (hyperplaneKernelRows_commRing A H).toCommMonoid.toCommSemigroup _ _ _

local instance hyperplaneKernelRows_localDifferentialModule (H : ι) :
    Module (A.hyperplaneLocalRing H) Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  KaehlerDifferential.module' ℂ (A.hyperplaneLocalRing H)

local instance hyperplaneKernelRows_localDifferentialSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  (hyperplaneKernelRows_localDifferentialModule A H).toSMul

local instance hyperplaneKernelRows_localDifferentialMulAction (H : ι) :
    MulAction (A.hyperplaneLocalRing H) Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  (hyperplaneKernelRows_localDifferentialModule A H).toDistribMulAction.toMulAction

local instance hyperplaneKernelRows_localDifferentialSelfComm (H : ι) :
    SMulCommClass (A.hyperplaneLocalRing H) (A.hyperplaneLocalRing H)
      Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  smulCommClass_self (A.hyperplaneLocalRing H) Ω[A.hyperplaneLocalRing H⁄ℂ]

local instance hyperplaneKernelRows_regularTensorModule (H : ι) :
    Module (A.hyperplaneLocalRing H)
      (Ω[A.hyperplaneLocalRing H⁄ℂ] ⊗[A.hyperplaneLocalRing H] Ω[A.hyperplaneLocalRing H⁄ℂ]) :=
  TensorProduct.leftModule

local instance hyperplaneKernelRows_regularTensorSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H)
      (Ω[A.hyperplaneLocalRing H⁄ℂ] ⊗[A.hyperplaneLocalRing H] Ω[A.hyperplaneLocalRing H⁄ℂ]) :=
  (hyperplaneKernelRows_regularTensorModule A H).toSMul

local instance hyperplaneKernelRows_localConstantComm (H : ι) :
    SMulCommClass ℂ ℂ (A.hyperplaneLocalRing H) where
  smul_comm c e f := by
    simp only [Algebra.smul_def]
    exact @mul_left_comm _ (hyperplaneKernelRows_commRing A H).toCommMonoid.toCommSemigroup _ _ _

local instance hyperplaneKernelRows_localConstantDifferentialModule (H : ι) :
    Module ℂ Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  KaehlerDifferential.module' ℂ (A.hyperplaneLocalRing H)

local instance hyperplaneKernelRows_pivotConstantComm (j : Fin d) :
    SMulCommClass ℂ ℂ (HyperplanePivotField j) where
  smul_comm c e f := by
    change algebraMap ℂ (HyperplanePivotField j) c *
        (algebraMap ℂ (HyperplanePivotField j) e * f) =
      algebraMap ℂ (HyperplanePivotField j) e *
        (algebraMap ℂ (HyperplanePivotField j) c * f)
    exact mul_left_comm _ _ _

local instance hyperplaneKernelRows_pivotDifferentialModule (j : Fin d) :
    Module ℂ Ω[HyperplanePivotField j⁄ℂ] :=
  KaehlerDifferential.module' ℂ (HyperplanePivotField j)

local instance hyperplaneKernelRows_twoFormFieldModule :
    Module (RationalFunctionField (d := d)) (RationalTwoForms (d := d)) :=
  exteriorTwoFormNativeFieldModule ℂ (RationalFunctionField (d := d))

local instance hyperplaneKernelRows_twoFormFieldSMul :
    SMul (RationalFunctionField (d := d)) (RationalTwoForms (d := d)) :=
  (hyperplaneKernelRows_twoFormFieldModule (d := d)).toSMul

local instance hyperplaneKernelRows_twoFormFieldMulAction :
    MulAction (RationalFunctionField (d := d)) (RationalTwoForms (d := d)) :=
  (hyperplaneKernelRows_twoFormFieldModule (d := d)).toDistribMulAction.toMulAction

local instance hyperplaneKernelRows_twoFormModule (H : ι) :
    Module (A.hyperplaneLocalRing H) (RationalTwoForms (d := d)) :=
  exteriorTwoFormModuleRestriction ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))

local instance hyperplaneKernelRows_twoFormSMul (H : ι) :
    SMul (A.hyperplaneLocalRing H) (RationalTwoForms (d := d)) :=
  (hyperplaneKernelRows_twoFormModule A H).toSMul

local instance hyperplaneKernelRows_constantTower (H : ι) :
    IsScalarTower ℂ (A.hyperplaneLocalRing H) (RationalTwoForms (d := d)) where
  smul_assoc c a w := by
    change algebraMap (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
        (algebraMap ℂ (A.hyperplaneLocalRing H) c * a) • w =
      algebraMap ℂ (RationalFunctionField (d := d)) c •
        (algebraMap (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) a • w)
    rw [map_mul, ← IsScalarTower.algebraMap_apply ℂ (A.hyperplaneLocalRing H)
      (RationalFunctionField (d := d))]
    exact mul_smul _ _ _

/-- A concrete regular logarithmic lift obtained by discarding the original
H-coordinate and using the actual other-equation local units. -/
def hyperplaneComplementRegularLog (H : ι) (x : ι → ℂ) :
    Ω[A.hyperplaneLocalRing H⁄ℂ] :=
  ∑ K : {K : ι // K ≠ H}, x K.val •
    A.hyperplaneOtherEquationRegularLog H K.val K.property.symm

/-- For an actual vector whose H-coordinate vanishes, the concrete local
lift maps to exactly its original rational logarithmic realization. -/
theorem hyperplaneComplementRegularLog_map_fraction (H : ι) (x : ι → ℂ)
    (hx : x H = 0) :
    KaehlerDifferential.map ℂ ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))
      (A.hyperplaneComplementRegularLog H x) = A.logarithmicRealization x := by
  classical
  rw [hyperplaneComplementRegularLog, map_sum]
  simp only [LinearMap.map_smul_of_tower,
    A.hyperplaneOtherEquationRegularLog_map_fraction]
  rw [A.logarithmicRealization_apply, Fintype.sum_eq_add_sum_subtype_ne _ H,
    hx, zero_smul, zero_add]

omit [Fintype ι] in
private theorem exterior_map_wedge (f : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (x y : ι → ℂ) :
    exteriorPower.map 2 f (exteriorWedge (k := ℂ) x y) =
      exteriorWedge (k := ℂ) (f x) (f y) := by
  simp only [exteriorWedge, exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Every complementary quadratic image has an actual regular tensor
preimage in the same original local ring. This existence follows from
the actual exterior generators and the constructed regular logarithms. -/
theorem exists_hyperplaneComplementRegularTensor (H : ι) (z : ⋀[ℂ]^2 (ι → ℂ)) :
    ∃ τ : Ω[A.hyperplaneLocalRing H⁄ℂ] ⊗[A.hyperplaneLocalRing H]
        Ω[A.hyperplaneLocalRing H⁄ℂ],
      regularTwoFormMap ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) τ =
        A.quadraticLogarithmicRealization
          (exteriorPower.map 2 (Koszul.coordinateComplementProjection ℂ (ι → ℂ)
            (LinearMap.proj H) (Pi.single H 1)) z) := by
  classical
  let q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    Koszul.coordinateComplementProjection ℂ (ι → ℂ) (LinearMap.proj H) (Pi.single H 1)
  let t := A.quadraticLogarithmicRealization.comp (exteriorPower.map 2 q)
  let R : Submodule ℂ (RationalTwoForms (d := d)) :=
    (LinearMap.range (regularTwoFormMap ℂ (A.hyperplaneLocalRing H)
      (RationalFunctionField (d := d)))).restrictScalars ℂ
  have hpure (x y : ι → ℂ) : exteriorWedge (k := ℂ) x y ∈ R.comap t := by
    have hx : q x H = 0 :=
      Koszul.coordinateComplementProjection_coordinate_zero ℂ ι H x
    have hy : q y H = 0 :=
      Koszul.coordinateComplementProjection_coordinate_zero ℂ ι H y
    rw [Submodule.mem_comap]
    change t (exteriorWedge (k := ℂ) x y) ∈ LinearMap.range
      (regularTwoFormMap ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)))
    rw [LinearMap.mem_range]
    refine ⟨A.hyperplaneComplementRegularLog H (q x) ⊗ₜ[A.hyperplaneLocalRing H]
      A.hyperplaneComplementRegularLog H (q y), ?_⟩
    rw [regularTwoFormMap_tmul, A.hyperplaneComplementRegularLog_map_fraction H (q x) hx,
      A.hyperplaneComplementRegularLog_map_fraction H (q y) hy]
    change exteriorWedge (k := RationalFunctionField (d := d))
      (A.logarithmicRealization (q x)) (A.logarithmicRealization (q y)) =
        A.quadraticLogarithmicRealization (exteriorPower.map 2 q (exteriorWedge x y))
    rw [exterior_map_wedge, A.quadraticLogarithmicRealization_exteriorWedge]
  have htop : (⊤ : Submodule ℂ (⋀[ℂ]^2 (ι → ℂ))) ≤ R.comap t := by
    rw [← exteriorWedge_span (k := ℂ) (E := ι → ℂ)]
    apply Submodule.span_le.mpr
    rintro w ⟨x, y, rfl⟩
    exact hpure x y
  have hzmem : z ∈ R.comap t := htop Submodule.mem_top
  rw [Submodule.mem_comap] at hzmem
  change t z ∈ LinearMap.range
    (regularTwoFormMap ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d))) at hzmem
  exact LinearMap.mem_range.mp hzmem

/-- The actual contracted mixed term expands with exactly the original
coordinate row coefficients and the same original equation units. -/
theorem quadraticLogarithmicRealization_coordinateMixed (H : ι) (z : ⋀[ℂ]^2 (ι → ℂ)) :
    A.quadraticLogarithmicRealization
      (exteriorWedge (k := ℂ) (Pi.single H 1) (Koszul.coordinateExteriorRow ℂ ι H z)) =
      ∑ K : {K : ι // K ≠ H},
        algebraMap ℂ (A.hyperplaneLocalRing H) (Koszul.coordinateExteriorRow ℂ ι H z K.val) •
          exteriorWedge (k := RationalFunctionField (d := d))
            (logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit H))
            (logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit K.val)) := by
  classical
  rw [A.quadraticLogarithmicRealization_exteriorWedge, A.logarithmicRealization_basis,
    A.logarithmicRealization_apply, Fintype.sum_eq_add_sum_subtype_ne _ H,
    Koszul.coordinateExteriorRow_self_zero, zero_smul, zero_add]
  change (exteriorWedgeBilin (k := RationalFunctionField (d := d))
    (logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit H)))
      (∑ K : {K : ι // K ≠ H}, Koszul.coordinateExteriorRow ℂ ι H z K.val •
        logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit K.val)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [← IsScalarTower.algebraMap_smul (RationalFunctionField (d := d))
    (Koszul.coordinateExteriorRow ℂ ι H z K.val)
      (logarithmicDifferential ℂ (RationalFunctionField (d := d)) (A.equationUnit K.val)),
    map_smul, algebraMap_smul (A.hyperplaneLocalRing H)]
  rfl

/-- Every genuine original rational quadratic-kernel element satisfies
the actual restricted logarithmic row at every original hyperplane.
The regular tensor remainder and the residue are both constructed. -/
theorem rationalQuadraticKernel_pivot_logarithmic_rows
    (z : ⋀[ℂ]^2 (ι → ℂ)) (hz : z ∈ A.rationalQuadraticKernel)
    (H : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0) :
    ∑ K : {K : ι // K ≠ H}, Koszul.coordinateExteriorRow ℂ ι H z K.val •
      logarithmicDifferential ℂ (HyperplanePivotField j)
        (A.hyperplaneRestrictedEquationUnit H K.val K.property.symm j hj) = 0 := by
  classical
  obtain ⟨τ, hτ⟩ := A.exists_hyperplaneComplementRegularTensor H z
  have hdecomp := congrArg A.quadraticLogarithmicRealization
    (Koszul.exteriorCoordinateRow_decomposition ℂ (ι → ℂ)
      (LinearMap.proj H) (Pi.single H 1) z)
  have hz' : A.quadraticLogarithmicRealization z = 0 := hz
  rw [hz', map_add, ← hτ] at hdecomp
  change 0 = A.quadraticLogarithmicRealization
    (exteriorWedge (k := ℂ) (Pi.single H 1) (Koszul.coordinateExteriorRow ℂ ι H z)) +
      regularTwoFormMap ℂ (A.hyperplaneLocalRing H) (RationalFunctionField (d := d)) τ at hdecomp
  rw [A.quadraticLogarithmicRealization_coordinateMixed H z] at hdecomp
  exact A.hyperplaneTwoForm_relation_restricts_to_pivot_logarithmic_row
    H j hj (fun K ↦ Koszul.coordinateExteriorRow ℂ ι H z K.val) τ hdecomp.symm

end ChenRanks.AffineArrangement
