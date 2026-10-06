import ChenRanks.CentralDeconeCoordinates

/-!
# The actual affine decone of the original central arrangement

The actual original slice coordinates restrict every remaining original
central equation to an affine hyperplane. Original regular hyperplane
points, normalized by the chosen equation, prove these hyperplanes
distinct. Thus the affine arrangement is built from the original data,
with exactly the original labels except the chosen hyperplane.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
local instance centralDeconeArrangementDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The remaining original labels, with no repeated equations. -/
abbrev ActualCentralDeconeLabels (_A : AffineArrangement d ι) (i₀ : ι) :=
  {H : ι // H ≠ i₀}

def actualCentralDeconeNormal (i₀ : ι) (H : A.ActualCentralDeconeLabels i₀) :
    (Fin (A.actualCentralDeconeDimension i₀) → ℂ) →ₗ[ℂ] ℂ :=
  (A.normal H.val).comp (A.actualCentralDeconeDirectionMap i₀)

def actualCentralDeconeOffset (i₀ : ι) (H : A.ActualCentralDeconeLabels i₀) : ℂ :=
  -A.normal H.val (A.actualCentralSliceBase i₀)

/-- The affine equation is precisely the original equation evaluated
at the genuine slice embedding. -/
theorem actualCentralDeconeEquation_iff (i₀ : ι)
    (H : A.ActualCentralDeconeLabels i₀)
    (x : Fin (A.actualCentralDeconeDimension i₀) → ℂ) :
    A.actualCentralDeconeNormal i₀ H x = A.actualCentralDeconeOffset i₀ H ↔
      A.normal H.val (A.actualCentralDeconeEmbedding i₀ x) = 0 := by
  change A.normal H.val (A.actualCentralDeconeDirectionMap i₀ x) =
      -A.normal H.val (A.actualCentralSliceBase i₀) ↔ _
  simp only [actualCentralDeconeEmbedding, map_add]
  constructor
  · intro he
    rw [he, add_neg_cancel]
  · intro he
    calc
      A.normal H.val (A.actualCentralDeconeDirectionMap i₀ x) =
        (A.normal H.val (A.actualCentralSliceBase i₀) +
          A.normal H.val (A.actualCentralDeconeDirectionMap i₀ x)) -
            A.normal H.val (A.actualCentralSliceBase i₀) := by abel
      _ = -A.normal H.val (A.actualCentralSliceBase i₀) := by rw [he, zero_sub]

variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)

include hcentral in
/-- Distinctness is proved on actual original normalized regular points,
not inherited through an unproved affine decone identification. -/
theorem actualCentralDeconeEquations_distinct :
    Pairwise fun H K : A.ActualCentralDeconeLabels i₀ =>
      {x | A.actualCentralDeconeNormal i₀ H x = A.actualCentralDeconeOffset i₀ H} ≠
      {x | A.actualCentralDeconeNormal i₀ K x = A.actualCentralDeconeOffset i₀ K} := by
  intro H K hHK heq
  have hKH : K.val ≠ H.val := by
    intro hv
    exact hHK (Subtype.ext hv.symm)
  obtain ⟨y, hy, havoid⟩ := A.exists_actual_meridian_center H.val
  have hyH : A.normal H.val y = 0 := by simpa only [hcentral H.val] using hy
  have hy₀ : A.normal i₀ y ≠ 0 := by
    simpa only [hcentral i₀] using havoid i₀ H.property.symm
  have hyK : A.normal K.val y ≠ 0 := by
    simpa only [hcentral K.val] using havoid K.val hKH
  let z := (A.normal i₀ y)⁻¹ • y
  have hz₀ : A.normal i₀ z = 1 := by
    change A.normal i₀ ((A.normal i₀ y)⁻¹ • y) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy₀]
  have hzH : A.normal H.val z = 0 := by
    simp only [z, map_smul, smul_eq_mul, hyH, mul_zero]
  have hzK : A.normal K.val z ≠ 0 := by
    change A.normal K.val ((A.normal i₀ y)⁻¹ • y) ≠ 0
    rw [map_smul, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hy₀) hyK
  let x := A.actualCentralDeconeCoordinate i₀ z hz₀
  have hxH : x ∈ {x | A.actualCentralDeconeNormal i₀ H x =
      A.actualCentralDeconeOffset i₀ H} := by
    apply (A.actualCentralDeconeEquation_iff i₀ H x).mpr
    rw [A.actualCentralDeconeEmbedding_coordinate i₀ z hz₀]
    exact hzH
  have hxK : x ∈ {x | A.actualCentralDeconeNormal i₀ K x =
      A.actualCentralDeconeOffset i₀ K} := heq ▸ hxH
  apply hzK
  have h := (A.actualCentralDeconeEquation_iff i₀ K x).mp hxK
  rw [A.actualCentralDeconeEmbedding_coordinate i₀ z hz₀] at h
  exact h

/-- The genuine affine decone, constructed with all original arrangement
requirements proved from the original central equations. -/
def actualCentralDecone : AffineArrangement (A.actualCentralDeconeDimension i₀)
    (A.ActualCentralDeconeLabels i₀) where
  normal := A.actualCentralDeconeNormal i₀
  offset := A.actualCentralDeconeOffset i₀
  normal_ne_zero H := A.actualCentralDeconeNormal_ne_zero hcentral i₀ H.val H.property
  distinct := A.actualCentralDeconeEquations_distinct hcentral i₀

/-- The genuine decone has exactly one fewer original hyperplane. -/
theorem actualCentralDecone_card :
    Fintype.card (A.ActualCentralDeconeLabels i₀) = Fintype.card ι - 1 := by
  letI : Unique {H : ι // H = i₀} :=
    { default := ⟨i₀, rfl⟩, uniq := fun H => Subtype.ext H.property }
  change Fintype.card {H : ι // ¬H = i₀} = Fintype.card ι - 1
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]

end ChenRanks.AffineArrangement
