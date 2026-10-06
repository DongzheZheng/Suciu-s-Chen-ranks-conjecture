import ChenRanks.KoszulThirdDifferential
import Mathlib.Algebra.Module.FinitePresentation

/-!
# A genuine finite presentation of the original Koszul module

The original module remains `ker δ₁ / im δ₂|K`.  The map from the actual
second tensor term is constructed from its original quotient map.  Actual
Koszul exactness identifies its kernel with the actual images of `δ₃` and
the given quadratic subspace.  The resulting cokernel is then proved
equivalent to the original module; this equivalence is not a definition.

No finite-presentation premise, resonance assertion, or Chen comparison
is used.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V))

/-- The actual polynomial extension of the original quadratic subspace inclusion. -/
def quadraticInclusion : S k V ⊗[k] K →ₗ[S k V] C2 k V :=
  AlgebraTensorModule.lTensor (S k V) (S k V) K.subtype

@[simp] theorem quadraticInclusion_tmul (s : S k V) (w : K) :
    quadraticInclusion k V K (s ⊗ₜ[k] w) = s ⊗ₜ[k] (w : ⋀[k]^2 V) := rfl

/-- The actual third differential and actual quadratic inclusion form the
relation map for the actual second tensor term. -/
def presentationRelations : (C3 k V × (S k V ⊗[k] K)) →ₗ[S k V] C2 k V :=
  (delta3 k V).coprod (quadraticInclusion k V K)

@[simp] theorem presentationRelations_apply (y : C3 k V) (x : S k V ⊗[k] K) :
    presentationRelations k V K (y, x) = delta3 k V y + quadraticInclusion k V K x := rfl

/-- The genuine map to the original `ker δ₁ / im δ₂|K` quotient. -/
def secondTensorToModule : C2 k V →ₗ[S k V] Module k V K :=
  (LinearMap.range (relationMap k V K)).mkQ ∘ₗ delta2ToCycles k V

theorem delta2ToCycles_quadraticInclusion (x : S k V ⊗[k] K) :
    delta2ToCycles k V (quadraticInclusion k V K x) = relationMap k V K x := rfl

@[simp] theorem secondTensorToModule_quadraticInclusion (x : S k V ⊗[k] K) :
    secondTensorToModule k V K (quadraticInclusion k V K x) = 0 := by
  change (Submodule.Quotient.mk (delta2ToCycles k V (quadraticInclusion k V K x)) :
    Module k V K) = 0
  rw [delta2ToCycles_quadraticInclusion, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ _

@[simp] theorem secondTensorToModule_delta3 (y : C3 k V) :
    secondTensorToModule k V K (delta3 k V y) = 0 := by
  have he : delta2ToCycles k V (delta3 k V y) = 0 := by
    apply Subtype.ext
    exact DFunLike.congr_fun (delta2_comp_delta3 k V) y
  change (LinearMap.range (relationMap k V K)).mkQ (delta2ToCycles k V (delta3 k V y)) = 0
  rw [he, map_zero]

theorem secondTensorToModule_comp_presentationRelations :
    secondTensorToModule k V K ∘ₗ presentationRelations k V K = 0 := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, presentationRelations, LinearMap.coprod_apply,
    map_add, secondTensorToModule_delta3, secondTensorToModule_quadraticInclusion,
    add_zero, LinearMap.zero_apply]

variable [FiniteDimensional k V] [CharZero k]

/-- Surjectivity onto the original quotient uses the already proved genuine
second-differential exactness. -/
theorem secondTensorToModule_surjective : Function.Surjective (secondTensorToModule k V K) :=
  (Submodule.mkQ_surjective (LinearMap.range (relationMap k V K))).comp
    (delta2ToCycles_surjective k V)

/-- The actual third differential and actual quadratic inclusion generate
the actual kernel of the map to the original module. -/
theorem secondTensorToModule_ker :
    LinearMap.ker (secondTensorToModule k V K) =
      LinearMap.range (presentationRelations k V K) := by
  ext z
  constructor
  · intro hz
    have hzero : (Submodule.Quotient.mk (delta2ToCycles k V z) : Module k V K) = 0 := hz
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (relationMap k V K))).mp hzero
    have hxval := congrArg Subtype.val hx
    change delta2 k V (quadraticInclusion k V K x) = delta2 k V z at hxval
    have hcycle : z - quadraticInclusion k V K x ∈ LinearMap.ker (delta2 k V) := by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, ← hxval, sub_self]
    rw [← delta3_exact k V] at hcycle
    obtain ⟨y, hy⟩ := hcycle
    exact ⟨(y, x), by rw [presentationRelations_apply, hy, sub_add_cancel]⟩
  · rintro ⟨⟨y, x⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    simp only [presentationRelations_apply, map_add, secondTensorToModule_delta3,
      secondTensorToModule_quadraticInclusion, add_zero]

/-- A proved cokernel description of the original module, with its genuine
polynomial scalar action. -/
def presentationEquiv :
    (C2 k V ⧸ LinearMap.range (presentationRelations k V K)) ≃ₗ[S k V] Module k V K :=
  (Submodule.quotEquivOfEq _ _ (secondTensorToModule_ker k V K).symm).trans
    ((secondTensorToModule k V K).quotKerEquivOfSurjective
      (secondTensorToModule_surjective k V K))

/-- The actual finite relations prove finite presentation of the original
module, without a Noetherianity or finite-presentation hypothesis. -/
theorem actual_koszulModule_finitePresentation :
    _root_.Module.FinitePresentation (S k V) (Module k V K) := by
  letI : _root_.Module.Finite (S k V) (C3 k V × (S k V ⊗[k] K)) := inferInstance
  apply _root_.Module.finitePresentation_of_free_of_surjective
    (secondTensorToModule k V K) (secondTensorToModule_surjective k V K)
  rw [secondTensorToModule_ker]
  exact Submodule.fg_range (presentationRelations k V K)

end ChenRanks.Koszul
