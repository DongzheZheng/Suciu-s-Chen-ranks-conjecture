import ChenRanks.KoszulPresentation
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Module.TransferInstance

/-!
# The genuine metabelian Lie model of the original Koszul module

The commutator coordinate is the existing quotient `ker δ₁ / im δ₂|K`,
with its existing action by `SymmetricAlgebra k V`. The bracket is the
actual formula on `V × Module k V K`. Its alternating constant term is
the class of `1 ⊗ (u ∧ v)`. The already proved third Koszul relation
proves Jacobi; neither Jacobi nor metabelianity is input data.

This constructs a genuine Lie algebra and kills the original quadratic
relations. It does not yet identify a free-Lie quotient with this model,
prove a graded Chen comparison, or assume a formality theorem.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V))

/-- Cache the native base-field module on the original quotient. -/
local instance canonicalKoszulQuotientBaseModule : _root_.Module k (Module k V K) :=
  Submodule.Quotient.module' (S := k) (LinearMap.range (relationMap k V K))

local instance canonicalKoszulQuotientBaseSMulZeroClass : SMulZeroClass k (Module k V K) :=
  Submodule.Quotient.smulZeroClass' (S := k) (LinearMap.range (relationMap k V K))

/-- The actual class map from constant second Koszul tensors. -/
def constantWedgeClass : (⋀[k]^2 V) →ₗ[k] Module k V K :=
  (secondTensorToModule k V K).restrictScalars k ∘ₗ
    TensorProduct.mk k (S k V) (⋀[k]^2 V) (1 : S k V)

@[simp]
theorem constantWedgeClass_apply (w : ⋀[k]^2 V) :
    constantWedgeClass k V K w =
      secondTensorToModule k V K ((1 : S k V) ⊗ₜ[k] w) := rfl

/-- The actual bilinear constant term of the bracket. -/
def wedgeClassBilinear : V →ₗ[k] V →ₗ[k] Module k V K :=
  (exteriorWedgeBilin (k := k) (E := V)).compr₂ (constantWedgeClass k V K)

@[simp]
theorem wedgeClassBilinear_apply (u v : V) :
    wedgeClassBilinear k V K u v =
      secondTensorToModule k V K ((1 : S k V) ⊗ₜ[k] exteriorWedge u v) := rfl

@[simp]
theorem wedgeClassBilinear_self (u : V) : wedgeClassBilinear k V K u u = 0 := by
  simp only [wedgeClassBilinear_apply, wedgeTwo_self, TensorProduct.tmul_zero, map_zero]

theorem wedgeClassBilinear_swap (u v : V) :
    wedgeClassBilinear k V K u v = -wedgeClassBilinear k V K v u := by
  simp only [wedgeClassBilinear_apply, wedgeTwo_swap k V u v,
    TensorProduct.tmul_neg, map_neg]

/-- Original quadratic relations vanish in the original quotient. -/
theorem constantWedgeClass_eq_zero_of_mem {w : ⋀[k]^2 V} (hw : w ∈ K) :
    constantWedgeClass k V K w = 0 := by
  exact secondTensorToModule_quadraticInclusion k V K
    ((1 : S k V) ⊗ₜ[k] (⟨w, hw⟩ : K))

/-- The actual third Koszul relation is the actual constant-term Jacobi identity. -/
theorem wedgeClassBilinear_jacobi (u v w : V) :
    SymmetricAlgebra.ι k V u • wedgeClassBilinear k V K v w -
      SymmetricAlgebra.ι k V v • wedgeClassBilinear k V K u w +
        SymmetricAlgebra.ι k V w • wedgeClassBilinear k V K u v = 0 := by
  have h := secondTensorToModule_delta3 k V K
    ((1 : S k V) ⊗ₜ[k] exteriorPower.ιMulti k 3 ![u, v, w])
  simpa only [delta3_tmul, one_smul, delta3Linear_wedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, map_add, map_sub, map_smul,
    wedgeClassBilinear_apply] using h

/-- A type distinct from the ambient product, carrying precisely its two
actual coordinates. No identity or universality assertion is a field. -/
structure MetabelianLieModel where
  generator : V
  invariant : Module k V K

namespace MetabelianLieModel

/-- The underlying coordinate equivalence to the original product. -/
def coordinateEquiv : MetabelianLieModel k V K ≃ V × Module k V K where
  toFun x := (x.generator, x.invariant)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance modelAddCommGroup : AddCommGroup (MetabelianLieModel k V K) :=
  (coordinateEquiv k V K).addCommGroup

instance modelModule : _root_.Module k (MetabelianLieModel k V K) :=
  (coordinateEquiv k V K).module k

@[ext]
theorem ext {x y : MetabelianLieModel k V K}
    (hgen : x.generator = y.generator) (hinv : x.invariant = y.invariant) : x = y := by
  cases x
  cases y
  cases hgen
  cases hinv
  rfl

@[simp] theorem generator_zero : (0 : MetabelianLieModel k V K).generator = 0 := rfl
@[simp] theorem invariant_zero : (0 : MetabelianLieModel k V K).invariant = 0 := rfl
@[simp] theorem generator_add (x y : MetabelianLieModel k V K) :
    (x + y).generator = x.generator + y.generator := rfl
@[simp] theorem invariant_add (x y : MetabelianLieModel k V K) :
    (x + y).invariant = x.invariant + y.invariant := rfl
@[simp] theorem generator_smul (c : k) (x : MetabelianLieModel k V K) :
    (c • x).generator = c • x.generator := rfl
@[simp] theorem invariant_smul (c : k) (x : MetabelianLieModel k V K) :
    (c • x).invariant = c • x.invariant := rfl

/-- The genuine bracket, using the existing symmetric-algebra action. -/
def bracketValue (x y : MetabelianLieModel k V K) : MetabelianLieModel k V K :=
  ⟨0, wedgeClassBilinear k V K x.generator y.generator +
    SymmetricAlgebra.ι k V x.generator • y.invariant -
      SymmetricAlgebra.ι k V y.generator • x.invariant⟩

private theorem bracketValue_add_left (x y z : MetabelianLieModel k V K) :
    bracketValue k V K (x + y) z =
      bracketValue k V K x z + bracketValue k V K y z := by
  apply ext
  · simp only [bracketValue, generator_add, add_zero]
  · simp only [bracketValue, generator_add, invariant_add, map_add,
      LinearMap.add_apply, add_smul, smul_add]
    abel

private theorem bracketValue_add_right (x y z : MetabelianLieModel k V K) :
    bracketValue k V K x (y + z) =
      bracketValue k V K x y + bracketValue k V K x z := by
  apply ext
  · simp only [bracketValue, generator_add, add_zero]
  · simp only [bracketValue, generator_add, invariant_add, map_add,
      add_smul, smul_add]
    abel

private theorem bracketValue_self (x : MetabelianLieModel k V K) :
    bracketValue k V K x x = 0 := by
  apply ext
  · rfl
  · simp only [bracketValue, wedgeClassBilinear_self, zero_add,
      sub_self, invariant_zero]

private theorem bracketValue_leibniz (x y z : MetabelianLieModel k V K) :
    bracketValue k V K x (bracketValue k V K y z) =
      bracketValue k V K (bracketValue k V K x y) z +
        bracketValue k V K y (bracketValue k V K x z) := by
  have hj := wedgeClassBilinear_jacobi k V K x.generator y.generator z.generator
  have hj' : SymmetricAlgebra.ι k V x.generator •
      wedgeClassBilinear k V K y.generator z.generator =
        SymmetricAlgebra.ι k V y.generator •
          wedgeClassBilinear k V K x.generator z.generator -
        SymmetricAlgebra.ι k V z.generator •
          wedgeClassBilinear k V K x.generator y.generator := by
    apply sub_eq_zero.mp
    calc
      _ = SymmetricAlgebra.ι k V x.generator •
          wedgeClassBilinear k V K y.generator z.generator -
          SymmetricAlgebra.ι k V y.generator •
            wedgeClassBilinear k V K x.generator z.generator +
          SymmetricAlgebra.ι k V z.generator •
            wedgeClassBilinear k V K x.generator y.generator := by abel
      _ = 0 := hj
  apply ext
  · simp only [bracketValue, generator_add, add_zero]
  · simp only [bracketValue, invariant_add, map_zero, LinearMap.zero_apply,
      zero_smul, add_zero, zero_add, sub_zero, smul_add, smul_sub]
    rw [hj']
    simp only [smul_smul, mul_comm]
    abel

instance modelLieRing : LieRing (MetabelianLieModel k V K) where
  toAddCommGroup := modelAddCommGroup k V K
  bracket := bracketValue k V K
  add_lie := bracketValue_add_left k V K
  lie_add := bracketValue_add_right k V K
  lie_self := bracketValue_self k V K
  leibniz_lie := bracketValue_leibniz k V K

instance modelLieAlgebra : LieAlgebra k (MetabelianLieModel k V K) where
  toModule := modelModule k V K
  lie_smul c x y := by
    change bracketValue k V K x (c • y) = c • bracketValue k V K x y
    apply ext
    · simp only [bracketValue, generator_smul, smul_zero]
    · simp only [bracketValue, generator_smul, invariant_smul, map_smul,
        smul_add, smul_sub, smul_assoc]
      rw [smul_comm (SymmetricAlgebra.ι k V x.generator) c]

@[simp] theorem generator_bracket (x y : MetabelianLieModel k V K) :
    (⁅x, y⁆ : MetabelianLieModel k V K).generator = 0 := rfl

@[simp] theorem invariant_bracket (x y : MetabelianLieModel k V K) :
    (⁅x, y⁆ : MetabelianLieModel k V K).invariant =
      wedgeClassBilinear k V K x.generator y.generator +
        SymmetricAlgebra.ι k V x.generator • y.invariant -
          SymmetricAlgebra.ι k V y.generator • x.invariant := rfl

/-- The original vector space enters the actual generator coordinate linearly. -/
def generatorInclusion : V →ₗ[k] MetabelianLieModel k V K where
  toFun v := ⟨v, 0⟩
  map_add' v w := by
    apply ext
    · rfl
    · exact (add_zero (0 : Module k V K)).symm
  map_smul' c v := by
    apply ext
    · rfl
    · exact (smul_zero c).symm

/-- The existing Koszul module enters the actual invariant coordinate linearly. -/
def invariantInclusion : Module k V K →ₗ[k] MetabelianLieModel k V K where
  toFun b := ⟨0, b⟩
  map_add' b c := by
    apply ext
    · exact (add_zero (0 : V)).symm
    · rfl
  map_smul' c b := by
    apply ext
    · exact (smul_zero c).symm
    · rfl

@[simp] theorem generatorInclusion_generator (v : V) :
    (generatorInclusion k V K v).generator = v := rfl
@[simp] theorem generatorInclusion_invariant (v : V) :
    (generatorInclusion k V K v).invariant = 0 := rfl
@[simp] theorem invariantInclusion_generator (b : Module k V K) :
    (invariantInclusion k V K b).generator = 0 := rfl
@[simp] theorem invariantInclusion_invariant (b : Module k V K) :
    (invariantInclusion k V K b).invariant = b := rfl

theorem invariantInclusion_injective : Function.Injective (invariantInclusion k V K) := by
  intro b c h
  exact congrArg MetabelianLieModel.invariant h

/-- Generator brackets are the original constant second-tensor classes. -/
theorem generators_bracket (u v : V) :
    ⁅generatorInclusion k V K u, generatorInclusion k V K v⁆ =
      invariantInclusion k V K (wedgeClassBilinear k V K u v) := by
  apply ext
  · rfl
  · simp only [invariant_bracket, generatorInclusion_generator,
      generatorInclusion_invariant, invariantInclusion_invariant, smul_zero,
      add_zero, sub_zero]

/-- The action on the invariant coordinate is exactly the existing
symmetric-algebra generator action. -/
theorem generator_invariant_bracket (u : V) (b : Module k V K) :
    ⁅generatorInclusion k V K u, invariantInclusion k V K b⁆ =
      invariantInclusion k V K (SymmetricAlgebra.ι k V u • b) := by
  apply ext
  · rfl
  · simp only [invariant_bracket, generatorInclusion_generator,
      generatorInclusion_invariant, invariantInclusion_generator,
      invariantInclusion_invariant, map_zero, smul_zero, zero_add, sub_zero]

/-- The actual exterior bracket map on generators, as a genuine linear map. -/
def generatorBracketMap : (⋀[k]^2 V) →ₗ[k] MetabelianLieModel k V K :=
  (invariantInclusion k V K).comp (constantWedgeClass k V K)

theorem generatorBracketMap_exteriorWedge (u v : V) :
    generatorBracketMap k V K (exteriorWedge u v) =
      ⁅generatorInclusion k V K u, generatorInclusion k V K v⁆ := by
  rw [generators_bracket]
  rfl

/-- All original quadratic relations are killed by the actual generator bracket map. -/
theorem generatorBracketMap_eq_zero_of_mem {w : ⋀[k]^2 V} (hw : w ∈ K) :
    generatorBracketMap k V K w = 0 := by
  simp only [generatorBracketMap, LinearMap.comp_apply,
    constantWedgeClass_eq_zero_of_mem k V K hw, map_zero]

/-- The true vertical coordinate is an actual Lie ideal. -/
def invariantIdeal : LieIdeal k (MetabelianLieModel k V K) where
  carrier := {x | x.generator = 0}
  zero_mem' := rfl
  add_mem' hx hy := by
    change _ = 0 at hx hy ⊢
    simp only [generator_add, hx, hy, add_zero]
  smul_mem' c x hx := by
    change x.generator = 0 at hx
    change (c • x).generator = 0
    rw [generator_smul, hx, smul_zero]
  lie_mem := by intro x y _hy; rfl

@[simp]
theorem mem_invariantIdeal (x : MetabelianLieModel k V K) :
    x ∈ invariantIdeal k V K ↔ x.generator = 0 := Iff.rfl

theorem bracket_eq_zero_of_generator_eq_zero {x y : MetabelianLieModel k V K}
    (hx : x.generator = 0) (hy : y.generator = 0) : ⁅x, y⁆ = 0 := by
  apply ext
  · rfl
  · simp only [invariant_bracket, hx, hy, map_zero,
      zero_smul, zero_add, sub_zero, invariant_zero]

/-- The original derived ideal is contained in the actual Koszul coordinate. -/
theorem derived_one_le_invariantIdeal :
    LieAlgebra.derivedSeries k (MetabelianLieModel k V K) 1 ≤ invariantIdeal k V K := by
  change ⁅(⊤ : LieIdeal k (MetabelianLieModel k V K)), ⊤⁆ ≤ invariantIdeal k V K
  rw [LieSubmodule.lie_le_iff]
  intro x _hx y _hy
  rfl

/-- Metabelianity is a conclusion about the original native derived series. -/
theorem derived_two_eq_bot :
    LieAlgebra.derivedSeries k (MetabelianLieModel k V K) 2 = ⊥ := by
  apply le_bot_iff.mp
  change ⁅LieAlgebra.derivedSeries k (MetabelianLieModel k V K) 1,
    LieAlgebra.derivedSeries k (MetabelianLieModel k V K) 1⁆ ≤ ⊥
  rw [LieSubmodule.lie_le_iff]
  intro x hx y hy
  have hx' : x.generator = 0 := derived_one_le_invariantIdeal k V K hx
  have hy' : y.generator = 0 := derived_one_le_invariantIdeal k V K hy
  rw [LieSubmodule.mem_bot]
  exact bracket_eq_zero_of_generator_eq_zero k V K hx' hy'

/-- In particular, brackets of two actual commutators vanish. -/
theorem commutators_bracket_eq_zero (x y z w : MetabelianLieModel k V K) :
    ⁅⁅x, y⁆, ⁅z, w⁆⁆ = 0 :=
  bracket_eq_zero_of_generator_eq_zero k V K rfl rfl

end MetabelianLieModel

end ChenRanks.Koszul
