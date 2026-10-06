import ChenRanks.GroupAlgebraAugmentationCotangent
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Genuine first-order augmentation and the original abelianization.
The maps are constructed from native group abelianization, native tensor
scalar extension and the proved actual I/I² universal property. The
inverse identities are proved on original group elements and actual
tensor generators. No higher dimension-subgroup or Chen/holonomy
comparison is asserted.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]

abbrev scalarAbelianization := k ⊗[ℤ] Additive (Abelianization G)

def scalarAbelianizationCharacter : Additive G →+ scalarAbelianization k G where
  toFun g := (1 : k) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g.toMul)
  map_zero' := by
    change (1 : k) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of (1 : G)) = 0
    rw [MonoidHom.map_one]
    change (1 : k) ⊗ₜ[ℤ] (0 : Additive (Abelianization G)) = 0
    simp only [TensorProduct.tmul_zero]
  map_add' g h := by
    change (1 : k) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of (g.toMul * h.toMul)) = _
    rw [MonoidHom.map_mul]
    exact TensorProduct.tmul_add _ _ _

def cotangentToScalarAbelianization :
    augmentationCotangent k G →ₗ[k] scalarAbelianization k G :=
  augmentationCotangentLift k G (scalarAbelianization k G)
    (scalarAbelianizationCharacter k G)

@[simp] theorem cotangentToScalarAbelianization_class (g : G) :
    cotangentToScalarAbelianization k G (augmentationCotangentClass k G g) =
      (1 : k) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g) :=
  augmentationCotangentLift_class k G (scalarAbelianization k G)
    (scalarAbelianizationCharacter k G) g

def cotangentGroupCharacter : G →* Multiplicative (augmentationCotangent k G) where
  toFun g := Multiplicative.ofAdd (augmentationCotangentClass k G g)
  map_one' := (augmentationCotangentCharacter k G).map_zero
  map_mul' g h := (augmentationCotangentCharacter k G).map_add _ _

def abelianizationCotangentCharacter : Additive (Abelianization G) →+ augmentationCotangent k G where
  toFun a := Multiplicative.toAdd
    (Abelianization.lift (cotangentGroupCharacter k G) a.toMul)
  map_zero' := (Abelianization.lift (cotangentGroupCharacter k G)).map_one
  map_add' a b := (Abelianization.lift (cotangentGroupCharacter k G)).map_mul _ _

@[simp] theorem abelianizationCotangentCharacter_of (g : G) :
    abelianizationCotangentCharacter k G (Additive.ofMul (Abelianization.of g)) =
      augmentationCotangentClass k G g := by
  change Multiplicative.toAdd
    (Abelianization.lift (cotangentGroupCharacter k G) (Abelianization.of g)) = _
  rw [Abelianization.lift_apply_of]
  rfl

def scalarAbelianizationToCotangent :
    scalarAbelianization k G →ₗ[k] augmentationCotangent k G :=
  AlgebraTensorModule.lift (R := ℤ) (A := k) (M := k)
    (N := Additive (Abelianization G)) (P := augmentationCotangent k G)
    (LinearMap.toSpanSingleton k
      (Additive (Abelianization G) →ₗ[ℤ] augmentationCotangent k G)
      (abelianizationCotangentCharacter k G).toIntLinearMap)

@[simp] theorem scalarAbelianizationToCotangent_tmul (c : k)
    (a : Additive (Abelianization G)) :
    scalarAbelianizationToCotangent k G (c ⊗ₜ[ℤ] a) =
      c • abelianizationCotangentCharacter k G a := by
  simp only [scalarAbelianizationToCotangent, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, AddMonoidHom.coe_toIntLinearMap]

theorem augmentationCotangent_scalarAbelianization_leftInverse :
    Function.LeftInverse (scalarAbelianizationToCotangent k G)
      (cotangentToScalarAbelianization k G) := by
  have h : (scalarAbelianizationToCotangent k G).comp
      (cotangentToScalarAbelianization k G) = LinearMap.id := by
    apply LinearMap.ext_on (augmentationCotangentClass_span k G)
    rintro _ ⟨g, rfl⟩
    simp only [LinearMap.comp_apply, cotangentToScalarAbelianization_class,
      scalarAbelianizationToCotangent_tmul, abelianizationCotangentCharacter_of,
      one_smul, LinearMap.id_apply]
  intro z
  exact LinearMap.congr_fun h z

theorem augmentationCotangent_scalarAbelianization_rightInverse :
    Function.RightInverse (scalarAbelianizationToCotangent k G)
      (cotangentToScalarAbelianization k G) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [(scalarAbelianizationToCotangent k G).map_zero,
      (cotangentToScalarAbelianization k G).map_zero]
  | tmul c a =>
    have hs : Function.Surjective (Abelianization.of : G →* Abelianization G) :=
      QuotientGroup.mk_surjective
    obtain ⟨g, hg⟩ := hs a.toMul
    have ha : a = Additive.ofMul (Abelianization.of g) := by
      exact congrArg Additive.ofMul hg.symm
    rw [ha, scalarAbelianizationToCotangent_tmul,
      abelianizationCotangentCharacter_of, map_smul,
      cotangentToScalarAbelianization_class, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add z w hz hw =>
    rw [(scalarAbelianizationToCotangent k G).map_add,
      (cotangentToScalarAbelianization k G).map_add, hz, hw]

/-- A genuine native linear equivalence, preserving all original group
classes in degree one. It makes no higher-rank assertion. -/
def augmentationCotangentScalarAbelianizationEquiv :
    augmentationCotangent k G ≃ₗ[k] scalarAbelianization k G :=
  LinearEquiv.ofLinear (cotangentToScalarAbelianization k G)
    (scalarAbelianizationToCotangent k G)
    (LinearMap.ext fun z => augmentationCotangent_scalarAbelianization_rightInverse k G z)
    (LinearMap.ext fun z => augmentationCotangent_scalarAbelianization_leftInverse k G z)

end ChenRanks.GroupAlgebra
