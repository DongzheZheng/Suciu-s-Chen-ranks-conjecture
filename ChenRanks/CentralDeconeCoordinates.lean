import ChenRanks.CentralSliceDeconing
import ChenRanks.ArrangementNonparallelNormalPair

/-!
# Genuine affine coordinates on the original central slice

The original chosen nonzero normal supplies an actual point of value
one. Its actual kernel, with its genuine finite-dimensional basis,
parametrizes the original slice by translation. These maps and their
inverse identities are derived from the original linear equations.
Distinctness of the central hyperplanes ensures that every remaining
normal has a genuinely nonzero restriction to that kernel.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- An actual point where the chosen original normal has value one. -/
def actualCentralSliceBase (i₀ : ι) : Fin d → ℂ :=
  (A.exists_actual_meridian_normal_vector i₀).choose

@[simp] theorem actualCentralSliceBase_value (i₀ : ι) :
    A.normal i₀ (A.actualCentralSliceBase i₀) = 1 :=
  (A.exists_actual_meridian_normal_vector i₀).choose_spec

/-- The actual direction space of the chosen original slice. -/
abbrev ActualCentralSliceDirection (i₀ : ι) := LinearMap.ker (A.normal i₀)

/-- Its genuine coordinate dimension, independent of a claimed ambient
dimension formula. The Chen range only uses the number of hyperplanes. -/
def actualCentralDeconeDimension (i₀ : ι) : ℕ :=
  Module.finrank ℂ (A.ActualCentralSliceDirection i₀)

/-- The actual native basis coordinates on the actual original kernel. -/
def actualCentralSliceCoordinates (i₀ : ι) :
    A.ActualCentralSliceDirection i₀ ≃ₗ[ℂ]
      (Fin (A.actualCentralDeconeDimension i₀) → ℂ) :=
  (Module.finBasis ℂ (A.ActualCentralSliceDirection i₀)).equivFun

/-- Include genuine direction coordinates in the original ambient space. -/
def actualCentralDeconeDirectionMap (i₀ : ι) :
    (Fin (A.actualCentralDeconeDimension i₀) → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  (A.ActualCentralSliceDirection i₀).subtype.comp
    (A.actualCentralSliceCoordinates i₀).symm.toLinearMap

@[simp] theorem actualCentralDeconeDirectionMap_normal (i₀ : ι)
    (x : Fin (A.actualCentralDeconeDimension i₀) → ℂ) :
    A.normal i₀ (A.actualCentralDeconeDirectionMap i₀ x) = 0 :=
  ((A.actualCentralSliceCoordinates i₀).symm x).property

/-- Translation by the original value-one point gives the genuine slice. -/
def actualCentralDeconeEmbedding (i₀ : ι)
    (x : Fin (A.actualCentralDeconeDimension i₀) → ℂ) : Fin d → ℂ :=
  A.actualCentralSliceBase i₀ + A.actualCentralDeconeDirectionMap i₀ x

@[simp] theorem actualCentralDeconeEmbedding_normal (i₀ : ι)
    (x : Fin (A.actualCentralDeconeDimension i₀) → ℂ) :
    A.normal i₀ (A.actualCentralDeconeEmbedding i₀ x) = 1 := by
  simp only [actualCentralDeconeEmbedding, map_add,
    A.actualCentralSliceBase_value, A.actualCentralDeconeDirectionMap_normal, add_zero]

/-- The actual inverse coordinate of an actual original value-one point. -/
def actualCentralDeconeCoordinate (i₀ : ι) (z : Fin d → ℂ)
    (hz : A.normal i₀ z = 1) : Fin (A.actualCentralDeconeDimension i₀) → ℂ :=
  A.actualCentralSliceCoordinates i₀
    ⟨z - A.actualCentralSliceBase i₀, by
      change A.normal i₀ (z - A.actualCentralSliceBase i₀) = 0
      rw [map_sub, hz, A.actualCentralSliceBase_value, sub_self]⟩

@[simp] theorem actualCentralDeconeEmbedding_coordinate (i₀ : ι)
    (z : Fin d → ℂ) (hz : A.normal i₀ z = 1) :
    A.actualCentralDeconeEmbedding i₀ (A.actualCentralDeconeCoordinate i₀ z hz) = z := by
  change A.actualCentralSliceBase i₀ +
    ((A.actualCentralSliceCoordinates i₀).symm
      (A.actualCentralSliceCoordinates i₀
        (⟨z - A.actualCentralSliceBase i₀, by
          change A.normal i₀ (z - A.actualCentralSliceBase i₀) = 0
          rw [map_sub, hz, A.actualCentralSliceBase_value, sub_self]⟩ :
            A.ActualCentralSliceDirection i₀))).val = z
  rw [LinearEquiv.symm_apply_apply]
  change A.actualCentralSliceBase i₀ + (z - A.actualCentralSliceBase i₀) = z
  simp only [sub_eq_add_neg]
  rw [add_left_comm, add_neg_cancel, add_zero]

@[simp] theorem actualCentralDeconeCoordinate_embedding (i₀ : ι)
    (x : Fin (A.actualCentralDeconeDimension i₀) → ℂ) :
    A.actualCentralDeconeCoordinate i₀ (A.actualCentralDeconeEmbedding i₀ x)
      (A.actualCentralDeconeEmbedding_normal i₀ x) = x := by
  unfold actualCentralDeconeCoordinate actualCentralDeconeEmbedding
  have he : (⟨A.actualCentralSliceBase i₀ + A.actualCentralDeconeDirectionMap i₀ x -
      A.actualCentralSliceBase i₀, by
        change A.normal i₀ (A.actualCentralSliceBase i₀ +
          A.actualCentralDeconeDirectionMap i₀ x - A.actualCentralSliceBase i₀) = 0
        rw [map_sub, map_add, A.actualCentralSliceBase_value,
          A.actualCentralDeconeDirectionMap_normal]
        ring⟩ : A.ActualCentralSliceDirection i₀) =
      (A.actualCentralSliceCoordinates i₀).symm x := by
    apply Subtype.ext
    change A.actualCentralSliceBase i₀ + A.actualCentralDeconeDirectionMap i₀ x -
      A.actualCentralSliceBase i₀ = A.actualCentralDeconeDirectionMap i₀ x
    abel
  rw [he, LinearEquiv.apply_symm_apply]

variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)

include hcentral in
/-- Distinct original central hyperplanes have genuinely nonproportional
normals, witnessed by an original regular point of the remaining one. -/
theorem actualCentralNormal_nonproportional (H : ι) (hH : H ≠ i₀)
    (a : ℂ) : A.normal H ≠ a • A.normal i₀ := by
  intro he
  obtain ⟨y, hy, havoid⟩ := A.exists_actual_meridian_center H
  have hyH : A.normal H y = 0 := by simpa only [hcentral H] using hy
  have hy₀ : A.normal i₀ y ≠ 0 := by
    simpa only [hcentral i₀] using havoid i₀ hH.symm
  have hz := congrArg (fun f : (Fin d → ℂ) →ₗ[ℂ] ℂ => f y) he
  change A.normal H y = a * A.normal i₀ y at hz
  rw [hyH] at hz
  have ha : a = 0 := (mul_eq_zero.mp hz.symm).resolve_right hy₀
  apply A.normal_ne_zero H
  simpa only [ha, zero_smul] using he

include hcentral in
/-- Each remaining original equation restricts to a genuine affine
hyperplane, with nonzero normal derived from the original distinctness. -/
theorem actualCentralDeconeNormal_ne_zero (H : ι) (hH : H ≠ i₀) :
    (A.normal H).comp (A.actualCentralDeconeDirectionMap i₀) ≠ 0 := by
  intro hz
  obtain ⟨v₁, v₂, hv₁₀, hv₁H, hv₂₀, hv₂H⟩ :=
    A.exists_actual_normal_pair_coordinate_vectors i₀ H
      (A.actualCentralNormal_nonproportional hcentral i₀ H hH)
  let w : A.ActualCentralSliceDirection i₀ := ⟨v₂, hv₂₀⟩
  have he := LinearMap.congr_fun hz (A.actualCentralSliceCoordinates i₀ w)
  change A.normal H
    ((A.actualCentralSliceCoordinates i₀).symm
      (A.actualCentralSliceCoordinates i₀ w)).val = 0 at he
  rw [LinearEquiv.symm_apply_apply] at he
  change A.normal H v₂ = 0 at he
  exact one_ne_zero (hv₂H.symm.trans he)

end ChenRanks.AffineArrangement
