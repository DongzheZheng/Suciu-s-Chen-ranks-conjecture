import ChenRanks.ArrangementSmoothLogarithmicOneForms
import ChenRanks.OpenSmoothDifferentialForms
import ChenRanks.ComplexAffineRealCoordinates

/-!
# Original logarithmic generators inside the actual smooth form complex

The open set is the original finite arrangement complement.  The actual
logarithmic functions constructed by native real calculus are placed in
the genuine smooth-form module on that same domain.  Germ locality proves
that its actual cochain differential agrees with the previously proved
native ambient exterior derivative.  Thus the original finite generator
map is a genuine complex-linear map into closed one-forms.
This does not assert wedge relations, a CDGA quasi-isomorphism, formality,
or a Malcev/Chen comparison.
-/

noncomputable section


open scoped Topology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual original complement as an actual open subset. -/
def actualSmoothComplementOpen : TopologicalSpace.Opens (Fin d → ℂ) :=
  ⟨A.ambientComplementSet, A.ambientComplementSet_isOpen⟩

/-- The original logarithmic form, now in the actual smooth-form module. -/
def actualSmoothLogarithmicForm (H : ι) :
    OpenSmoothForms.SmoothForm A.actualSmoothComplementOpen 1 := by
  refine ⟨fun x => A.actualAmbientLogarithmicOneForm H x.val, ?_⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (OpenSmoothForms.zeroExtension A.actualSmoothComplementOpen 1
      (fun x => A.actualAmbientLogarithmicOneForm H x.val)) A.actualSmoothComplementOpen
  apply (A.actualAmbientLogarithmicOneForm_contDiffOn H).congr
  intro x hx
  exact OpenSmoothForms.zeroExtension_apply_mem A.actualSmoothComplementOpen 1
    (fun y => A.actualAmbientLogarithmicOneForm H y.val) x hx

@[simp] theorem actualSmoothLogarithmicForm_apply (H : ι)
    (x : A.actualSmoothComplementOpen) (v : Fin 1 → (Fin d → ℂ)) :
    A.actualSmoothLogarithmicForm H x v =
      (A.normal H x.val - A.offset H)⁻¹ * A.normal H (v 0) := rfl

/-- The form-complex representative and the original ambient form agree
on a genuine open neighborhood of every original complement point. -/
theorem actualSmoothLogarithmicForm_representative_eventuallyEq
    (H : ι) (x : A.actualSmoothComplementOpen) :
    OpenSmoothForms.zeroExtension A.actualSmoothComplementOpen 1
      (A.actualSmoothLogarithmicForm H).val =ᶠ[𝓝 x.val]
        A.actualAmbientLogarithmicOneForm H := by
  filter_upwards [A.ambientComplementSet_isOpen.mem_nhds x.property] with y hy
  rw [OpenSmoothForms.zeroExtension_apply_mem A.actualSmoothComplementOpen 1
    (A.actualSmoothLogarithmicForm H).val y hy]
  rfl

/-- Closedness in the actual smooth-form complex follows from the native
ambient computation and proved germ locality, with no closedness premise. -/
theorem actualSmoothLogarithmicForm_differential_eq_zero (H : ι) :
    OpenSmoothForms.differential A.actualSmoothComplementOpen 1
      (A.actualSmoothLogarithmicForm H) = 0 := by
  apply Subtype.ext
  funext x
  change extDeriv (OpenSmoothForms.zeroExtension A.actualSmoothComplementOpen 1
    (A.actualSmoothLogarithmicForm H).val) x.val = 0
  rw [extDeriv,
    (A.actualSmoothLogarithmicForm_representative_eventuallyEq H x).fderiv_eq]
  exact A.actualAmbientLogarithmicOneForm_extDeriv_eq_zero H x.val
    (sub_ne_zero.mpr (x.property H))

/-- The original finite generator space maps complex-linearly to actual
smooth logarithmic one-forms on the original complement. -/
def actualSmoothLogarithmicGeneratorMap :
    (ι → ℂ) →ₗ[ℂ] OpenSmoothForms.SmoothForm A.actualSmoothComplementOpen 1 :=
  ∑ H : ι, (LinearMap.proj H).smulRight (A.actualSmoothLogarithmicForm H)

@[simp] theorem actualSmoothLogarithmicGeneratorMap_apply (a : ι → ℂ) :
    A.actualSmoothLogarithmicGeneratorMap a =
      ∑ H : ι, a H • A.actualSmoothLogarithmicForm H := by
  simp [actualSmoothLogarithmicGeneratorMap]

/-- This actual degree-one map has zero actual cochain differential. -/
theorem actualSmoothLogarithmicGeneratorMap_differential_eq_zero :
    (OpenSmoothForms.differentialLinearMap A.actualSmoothComplementOpen 1).comp
      A.actualSmoothLogarithmicGeneratorMap = 0 := by
  apply LinearMap.ext
  intro a
  change (OpenSmoothForms.differentialLinearMap A.actualSmoothComplementOpen 1)
    (A.actualSmoothLogarithmicGeneratorMap a) = 0
  rw [actualSmoothLogarithmicGeneratorMap_apply, map_sum]
  have hz : ∀ H : ι,
      OpenSmoothForms.differentialLinearMap A.actualSmoothComplementOpen 1
        (A.actualSmoothLogarithmicForm H) = 0 :=
    A.actualSmoothLogarithmicForm_differential_eq_zero
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero]

end ChenRanks.AffineArrangement
