import ChenRanks.ArrangementEquationPhaseMaps
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Actual uniform neighborhoods of original arrangement paths

The finite original complement is open. Compactness of an actual path
therefore supplies a genuine uniform positive radius around its original
image. Pointwise-close original ambient paths and their explicit affine
interpolation remain in that same original complement. This is the
geometric margin needed for constructing polygonal approximations; no
approximation, meridian-generation, or H¹-spanning statement is assumed.
-/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual original complement as a subset of its ambient affine space. -/
def ambientComplementSet : Set (Fin d → ℂ) :=
  {x | ∀ H : ι, A.normal H x ≠ A.offset H}

/-- The actual finite set of original hyperplanes has an open complement. -/
theorem ambientComplementSet_isOpen : IsOpen A.ambientComplementSet := by
  have heq : A.ambientComplementSet = ⋂ H : ι, {x | A.normal H x ≠ A.offset H} := by
    ext x
    simp [ambientComplementSet]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro H
  exact isOpen_ne_fun (A.normal H).continuous_of_finiteDimensional continuous_const

/-- The genuine compact path image has a uniformly positive original
ambient tube contained in the original complement. -/
theorem exists_actual_path_avoidance_radius (γ : C(I, A.Complement)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : I) (x : Fin d → ℂ),
      dist x (γ t).val < ε → ∀ H : ι, A.normal H x ≠ A.offset H := by
  let f : I → (Fin d → ℂ) := fun t => (γ t).val
  have hf : Continuous f := continuous_subtype_val.comp γ.continuous
  have hK : IsCompact (Set.range f) := isCompact_range hf
  have hKU : Set.range f ⊆ A.ambientComplementSet := by
    rintro _ ⟨t, rfl⟩
    exact (γ t).property
  obtain ⟨ε, hε, hεU⟩ :=
    hK.exists_thickening_subset_open A.ambientComplementSet_isOpen hKU
  refine ⟨ε, hε, ?_⟩
  intro t x hx
  exact hεU (Metric.mem_thickening_iff.mpr ⟨f t, ⟨t, rfl⟩, hx⟩)

/-- This radius is selected from that actual proved compactness theorem. -/
def actualPathAvoidanceRadius (γ : C(I, A.Complement)) : ℝ :=
  (A.exists_actual_path_avoidance_radius γ).choose

theorem actualPathAvoidanceRadius_pos (γ : C(I, A.Complement)) :
    0 < A.actualPathAvoidanceRadius γ :=
  (A.exists_actual_path_avoidance_radius γ).choose_spec.1

theorem actualPathAvoidanceRadius_avoids (γ : C(I, A.Complement))
    (t : I) (x : Fin d → ℂ) (hx : dist x (γ t).val < A.actualPathAvoidanceRadius γ) :
    ∀ H : ι, A.normal H x ≠ A.offset H :=
  (A.exists_actual_path_avoidance_radius γ).choose_spec.2 t x hx

/-- The actual pointwise-close ambient path really takes values in the
same original complement. -/
def nearPathInComplement (γ : C(I, A.Complement)) (η : C(I, Fin d → ℂ))
    (hη : ∀ t, dist (η t) (γ t).val < A.actualPathAvoidanceRadius γ) :
    C(I, A.Complement) where
  toFun t := ⟨η t, A.actualPathAvoidanceRadius_avoids γ t (η t) (hη t)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact η.continuous

/-- Every actual affine interpolation point stays in the actual path's
genuine uniform tube. -/
theorem nearPathInterpolation_avoids (γ : C(I, A.Complement))
    (η : C(I, Fin d → ℂ))
    (hη : ∀ t, dist (η t) (γ t).val < A.actualPathAvoidanceRadius γ)
    (s t : I) :
    ∀ H : ι, A.normal H ((γ t).val + ((s : ℝ) : ℂ) • (η t - (γ t).val)) ≠ A.offset H := by
  apply A.actualPathAvoidanceRadius_avoids γ t
  have hdist : dist ((γ t).val + ((s : ℝ) : ℂ) • (η t - (γ t).val)) (γ t).val =
      (s : ℝ) * dist (η t) (γ t).val := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.property.1, dist_eq_norm]
  rw [hdist]
  exact (mul_le_of_le_one_left dist_nonneg s.property.2).trans_lt (hη t)

/-- The actual affine homotopy between the original path and its actual
nearby ambient path, constructed inside the original complement. -/
def nearPathInterpolation (γ : C(I, A.Complement)) (η : C(I, Fin d → ℂ))
    (hη : ∀ t, dist (η t) (γ t).val < A.actualPathAvoidanceRadius γ) :
    C(I × I, A.Complement) where
  toFun p := ⟨(γ p.2).val + ((p.1 : ℝ) : ℂ) • (η p.2 - (γ p.2).val),
    A.nearPathInterpolation_avoids γ η hη p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem nearPathInterpolation_zero (γ : C(I, A.Complement))
    (η : C(I, Fin d → ℂ))
    (hη : ∀ t, dist (η t) (γ t).val < A.actualPathAvoidanceRadius γ) (t : I) :
    A.nearPathInterpolation γ η hη (0, t) = γ t := by
  apply Subtype.ext
  change (γ t).val + (0 : ℂ) • (η t - (γ t).val) = (γ t).val
  rw [zero_smul, add_zero]

theorem nearPathInterpolation_one (γ : C(I, A.Complement))
    (η : C(I, Fin d → ℂ))
    (hη : ∀ t, dist (η t) (γ t).val < A.actualPathAvoidanceRadius γ) (t : I) :
    A.nearPathInterpolation γ η hη (1, t) = A.nearPathInComplement γ η hη t := by
  apply Subtype.ext
  change (γ t).val + (1 : ℂ) • (η t - (γ t).val) = η t
  rw [one_smul, add_sub_cancel]

/-- Two actual closed paths give an actual free-loop homotopy; there is
no assumption that their basepoints coincide. -/
theorem nearPathInterpolation_closed (γ : C(I, A.Complement))
    (η : C(I, Fin d → ℂ))
    (hη : ∀ t, dist (η t) (γ t).val < A.actualPathAvoidanceRadius γ)
    (hγ : γ 0 = γ 1) (hηclosed : η 0 = η 1) (s : I) :
    A.nearPathInterpolation γ η hη (s, 0) =
      A.nearPathInterpolation γ η hη (s, 1) := by
  apply Subtype.ext
  change (γ 0).val + ((s : ℝ) : ℂ) • (η 0 - (γ 0).val) =
    (γ 1).val + ((s : ℝ) : ℂ) • (η 1 - (γ 1).val)
  rw [hγ, hηclosed]

end ChenRanks.AffineArrangement
