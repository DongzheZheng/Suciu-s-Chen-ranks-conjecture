import ChenRanks.ArrangementObjects
import ChenRanks.LogarithmicDifferentials
import ChenRanks.ExteriorSeparation
import ChenRanks.ClosedRationalForms
import ChenRanks.LogarithmicRelations
import Mathlib

/-!
# Actual logarithmic forms of an affine arrangement

This implements the rational-form realization used in the paper's quadratic
arrangement section. Equations are actual polynomials obtained from the
linear maps and offsets of `AffineArrangement`. Their evaluation agrees with
the original affine equations, and each nonzero equation gives an actual unit
in the fraction field of the coordinate ring.

The target of the quadratic realization is the exterior square over the
function field, not the exterior square over the constant field. No
Orlik–Solomon or topological cup-product comparison is assumed here.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks
namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance : DecidableEq ι := Classical.decEq ι

/-- The actual coordinate ring of complex affine `d`-space. -/
abbrev CoordinateRing := MvPolynomial (Fin d) ℂ

/-- Its actual rational-function field. -/
abbrev RationalFunctionField := FractionRing (CoordinateRing (d := d))

instance rationalFunctionField_complexAlgebra : Algebra ℂ (RationalFunctionField (d := d)) :=
  ((algebraMap (CoordinateRing (d := d)) (RationalFunctionField (d := d))).comp
    MvPolynomial.C).toAlgebra

instance rationalFunctionField_complexSMul : SMul ℂ (RationalFunctionField (d := d)) :=
  (inferInstance : Algebra ℂ (RationalFunctionField (d := d))).toSMul

instance rationalFunctionField_complexScalarComm :
    SMulCommClass ℂ ℂ (RationalFunctionField (d := d)) where
  smul_comm c e f := by
    change algebraMap ℂ (RationalFunctionField (d := d)) c *
        (algebraMap ℂ (RationalFunctionField (d := d)) e * f) =
      algebraMap ℂ (RationalFunctionField (d := d)) e *
        (algebraMap ℂ (RationalFunctionField (d := d)) c * f)
    ring

instance rationalFunctionField_complexScalarTower :
    IsScalarTower ℂ ℂ (RationalFunctionField (d := d)) where
  smul_assoc a b x := by
    change algebraMap ℂ (RationalFunctionField (d := d)) (a * b) * x =
      algebraMap ℂ (RationalFunctionField (d := d)) a *
        (algebraMap ℂ (RationalFunctionField (d := d)) b * x)
    rw [map_mul, mul_assoc]

instance rationalFunctionField_coordinateTower :
    IsScalarTower ℂ (CoordinateRing (d := d)) (RationalFunctionField (d := d)) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := CoordinateRing (d := d))
    (A := RationalFunctionField (d := d)) fun _ ↦ rfl

/-- The actual configuration function field is essentially of finite type
over the constants, by polynomial finiteness and fraction localization. -/
instance rationalFunctionField_essFiniteType :
    Algebra.EssFiniteType ℂ (RationalFunctionField (d := d)) := by
  letI : Algebra.EssFiniteType (CoordinateRing (d := d))
      (RationalFunctionField (d := d)) :=
    Algebra.EssFiniteType.of_isLocalization
      (RationalFunctionField (d := d)) (nonZeroDivisors (CoordinateRing (d := d)))
  exact Algebra.EssFiniteType.comp ℂ (CoordinateRing (d := d))
    (RationalFunctionField (d := d))

instance rationalDifferentials_complexModule :
    Module ℂ Ω[RationalFunctionField (d := d)⁄ℂ] :=
  KaehlerDifferential.module' ℂ (RationalFunctionField (d := d))

/-- Actual rational two-forms, using exterior powers over the function field. -/
abbrev RationalTwoForms :=
  ⋀[RationalFunctionField (d := d)]^2 Ω[RationalFunctionField (d := d)⁄ℂ]

instance rationalTwoForms_addCommGroup : AddCommGroup (RationalTwoForms (d := d)) :=
  Submodule.addCommGroup _

instance rationalTwoForms_fieldModule :
    Module (RationalFunctionField (d := d)) (RationalTwoForms (d := d)) :=
  Submodule.module _

instance rationalTwoForms_complexModule : Module ℂ (RationalTwoForms (d := d)) :=
  Module.compHom (RationalTwoForms (d := d)) (algebraMap ℂ (RationalFunctionField (d := d)))

instance rationalTwoForms_complexSMul : SMul ℂ (RationalTwoForms (d := d)) :=
  (rationalTwoForms_complexModule (d := d)).toSMul

instance rationalTwoForms_scalarTower :
    IsScalarTower ℂ (RationalFunctionField (d := d)) (RationalTwoForms (d := d)) where
  smul_assoc c a ω := by
    change (algebraMap ℂ (RationalFunctionField (d := d)) c * a) • ω =
      algebraMap ℂ (RationalFunctionField (d := d)) c • (a • ω)
    exact mul_smul (algebraMap ℂ (RationalFunctionField (d := d)) c) a ω

/-- The polynomial defining the hyperplane indexed by `H`. -/
def equationPolynomial (H : ι) : CoordinateRing (d := d) :=
  (∑ i : Fin d,
    MvPolynomial.C (A.normal H (Pi.single i 1)) * MvPolynomial.X i) -
      MvPolynomial.C (A.offset H)

theorem normal_eq_coordinate_sum (H : ι) (x : Fin d → ℂ) :
    A.normal H x = ∑ i : Fin d, A.normal H (Pi.single i 1) * x i := by
  classical
  calc
    A.normal H x = A.normal H (∑ i : Fin d, Pi.single i (x i)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ i : Fin d, A.normal H (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i : Fin d, A.normal H (Pi.single i 1) * x i := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (Pi.single i (x i) : Fin d → ℂ) =
          x i • (Pi.single i (1 : ℂ) : Fin d → ℂ) := by
        ext j
        by_cases h : j = i
        · subst j
          simp
        · simp [h]
      rw [hi, map_smul, smul_eq_mul, mul_comm]

theorem equationPolynomial_eval (H : ι) (x : Fin d → ℂ) :
    MvPolynomial.eval x (A.equationPolynomial H) = A.normal H x - A.offset H := by
  classical
  simp [equationPolynomial, ← A.normal_eq_coordinate_sum H x]

theorem equationPolynomial_ne_zero (H : ι) : A.equationPolynomial H ≠ 0 := by
  intro hz
  have hzero : A.offset H = 0 := by
    have he := A.equationPolynomial_eval H 0
    simp [hz] at he
    exact he
  apply A.normal_ne_zero H
  apply LinearMap.ext
  intro x
  have he := A.equationPolynomial_eval H x
  simpa [hz, hzero] using he.symm

/-- The same equation viewed as an actual rational function. -/
def equationFunction (H : ι) : RationalFunctionField (d := d) :=
  algebraMap (CoordinateRing (d := d)) (RationalFunctionField (d := d))
    (A.equationPolynomial H)

theorem equationFunction_ne_zero (H : ι) : A.equationFunction H ≠ 0 := by
  intro hz
  apply A.equationPolynomial_ne_zero H
  exact IsFractionRing.injective (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) (by simpa [equationFunction] using hz)

/-- The actual nonzero rational function as a unit. -/
def equationUnit (H : ι) : (RationalFunctionField (d := d))ˣ :=
  Units.mk0 (A.equationFunction H) (A.equationFunction_ne_zero H)

theorem equationUnit_coe (H : ι) :
    (A.equationUnit H : RationalFunctionField (d := d)) = A.equationFunction H := rfl

/-- `Phi^1(e_H) = dlog L_H`, extended complex linearly. -/
def logarithmicRealization : (ι → ℂ) →ₗ[ℂ] Ω[RationalFunctionField (d := d)⁄ℂ] where
  toFun c := ∑ H, c H • logarithmicDifferential ℂ _ (A.equationUnit H)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem logarithmicRealization_apply (c : ι → ℂ) :
    A.logarithmicRealization c =
      ∑ H, c H • logarithmicDifferential ℂ _ (A.equationUnit H) := rfl

theorem logarithmicRealization_basis (H : ι) :
    A.logarithmicRealization (Pi.single H 1) =
      logarithmicDifferential ℂ _ (A.equationUnit H) := by
  classical
  simp [logarithmicRealization]

/-- Closedness of the actual arrangement forms follows from logarithmic
generation, as required in the paper's curve construction. -/
theorem logarithmicRealization_isClosed (c : ι → ℂ) :
    IsClosedRationalForm ℂ (RationalFunctionField (d := d))
      (A.logarithmicRealization c) :=
  logarithmicCombination_isClosed ℂ _ (A.equationUnit) c

/-- Integer combinations correspond to actual rational functions, including
negative powers. This is the product used in the vertical-function lemma. -/
theorem logarithmicRealization_integral (n : ι → ℤ) :
    A.logarithmicRealization (fun H ↦ (n H : ℂ)) =
      logarithmicDifferential ℂ _ (∏ H, A.equationUnit H ^ n H) := by
  rw [logarithmicDifferential_prod_zpow]
  simp only [logarithmicRealization, LinearMap.coe_mk, AddHom.coe_mk,
    Int.cast_smul_eq_zsmul]

/-- The genuine rational exterior product, restricted to constant scalars. -/
def rationalWedgeAlternating :
    Ω[RationalFunctionField (d := d)⁄ℂ] [⋀^Fin 2]→ₗ[ℂ]
      RationalTwoForms (d := d) where
  toMultilinearMap :=
    (exteriorPower.ιMulti (RationalFunctionField (d := d)) 2).toMultilinearMap.restrictScalars ℂ
  map_eq_zero_of_eq' := by
    intro a i j h hij
    exact (exteriorPower.ιMulti (RationalFunctionField (d := d)) 2).map_eq_zero_of_eq a h hij

/-- The actual quadratic rational-form realization, with constant-field
exterior power in the source and function-field exterior power in the target. -/
def quadraticLogarithmicRealization :
    (⋀[ℂ]^2 (ι → ℂ)) →ₗ[ℂ]
      RationalTwoForms (d := d) :=
  exteriorPower.alternatingMapLinearEquiv
    ((rationalWedgeAlternating (d := d)).compLinearMap A.logarithmicRealization)

theorem quadraticLogarithmicRealization_wedge (a : Fin 2 → ι → ℂ) :
    A.quadraticLogarithmicRealization (exteriorPower.ιMulti ℂ 2 a) =
      exteriorPower.ιMulti (RationalFunctionField (d := d)) 2
        (fun i => A.logarithmicRealization (a i)) := by
  simp [quadraticLogarithmicRealization, rationalWedgeAlternating]

theorem quadraticLogarithmicRealization_exteriorWedge (x y : ι → ℂ) :
    A.quadraticLogarithmicRealization (exteriorWedge (k := ℂ) x y) =
      exteriorWedge (k := RationalFunctionField (d := d))
        (A.logarithmicRealization x) (A.logarithmicRealization y) := by
  exact A.quadraticLogarithmicRealization_wedge ![x, y]

/-- The genuine degree-two boundary in the constant-field exterior algebra. -/
def tripleBoundary (H K L : ι) : ⋀[ℂ]^2 (ι → ℂ) :=
  exteriorWedge (k := ℂ) (Pi.single K 1) (Pi.single L 1) -
    exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single L 1) +
    exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)

/-- A constant linear relation among the actual defining polynomials gives
the corresponding linear relation in the actual function field. -/
theorem equationFunction_relation_of_polynomial_relation (H K L : ι) (a b : ℂ)
    (hw : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    A.equationFunction L =
      algebraMap ℂ (RationalFunctionField (d := d)) a * A.equationFunction H +
      algebraMap ℂ (RationalFunctionField (d := d)) b * A.equationFunction K := by
  simp only [equationFunction, hw, map_add, Algebra.smul_def, map_mul]
  rw [← IsScalarTower.algebraMap_apply ℂ (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) a,
    ← IsScalarTower.algebraMap_apply ℂ (CoordinateRing (d := d))
    (RationalFunctionField (d := d)) b]

/-- The first inclusion in the paper's logarithmic-kernel lemma, evaluated
on an actual triple satisfying its polynomial relation. -/
theorem quadraticLogarithmicRealization_tripleBoundary_eq_zero
    (H K L : ι) (a b : ℂ)
    (hw : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    A.quadraticLogarithmicRealization (tripleBoundary H K L) = 0 := by
  simp only [tripleBoundary, map_add, map_sub,
    quadraticLogarithmicRealization_exteriorWedge, logarithmicRealization_basis]
  apply logarithmic_triple_relation (A.equationUnit H) (A.equationUnit K)
    (A.equationUnit L) a b
  exact A.equationFunction_relation_of_polynomial_relation H K L a b hw

/-- The actual quadratic kernel of the rational realization. Identifying
this subspace with the topological cup-product kernel remains a theorem. -/
def rationalQuadraticKernel : Submodule ℂ (⋀[ℂ]^2 (ι → ℂ)) :=
  LinearMap.ker A.quadraticLogarithmicRealization

theorem exteriorWedge_mem_rationalQuadraticKernel_iff (x y : ι → ℂ) :
    exteriorWedge (k := ℂ) x y ∈ A.rationalQuadraticKernel ↔
      exteriorWedge (k := RationalFunctionField (d := d))
        (A.logarithmicRealization x) (A.logarithmicRealization y) = 0 := by
  simp only [rationalQuadraticKernel, LinearMap.mem_ker,
    quadraticLogarithmicRealization_exteriorWedge]

theorem tripleBoundary_mem_rationalQuadraticKernel (H K L : ι) (a b : ℂ)
    (hw : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    tripleBoundary H K L ∈ A.rationalQuadraticKernel :=
  A.quadraticLogarithmicRealization_tripleBoundary_eq_zero H K L a b hw

/-- In a central arrangement, an actual linear relation among the normals
induces the same relation among the actual defining polynomials. -/
theorem equationPolynomial_relation_of_central_normal_relation
    (hcentral : ∀ J, A.offset J = 0) (H K L : ι) (a b : ℂ)
    (hnormal : A.normal L = a • A.normal H + b • A.normal K) :
    A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K := by
  have he : ∀ i : Fin d, A.normal L (Pi.single i 1) =
      a * A.normal H (Pi.single i 1) + b * A.normal K (Pi.single i 1) := by
    intro i
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using
      DFunLike.congr_fun hnormal (Pi.single i 1)
  simp only [equationPolynomial, hcentral, map_zero, sub_zero, he,
    map_add, map_mul, add_mul, mul_assoc, Finset.sum_add_distrib,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum]

/-- The actual normal-span condition of a central rank-two block supplies
the polynomial relation; its coefficients are witnesses, not assumptions. -/
theorem tripleBoundary_mem_kernel_of_central_normal_span
    (hcentral : ∀ J, A.offset J = 0) (H K L : ι)
    (hspan : A.normal L ∈ Submodule.span ℂ {A.normal H, A.normal K}) :
    tripleBoundary H K L ∈ A.rationalQuadraticKernel := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
  exact A.tripleBoundary_mem_rationalQuadraticKernel H K L a b
    (A.equationPolynomial_relation_of_central_normal_relation hcentral H K L a b hab.symm)

end AffineArrangement
end ChenRanks
