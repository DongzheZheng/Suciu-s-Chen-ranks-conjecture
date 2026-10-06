import ChenRanks.CentralDeconeArrangement
import ChenRanks.CentralSliceChenReduction

/-!
# Actual complement and Chen-space reduction through the actual affine decone

The original central slice and the constructed original affine decone
are homeomorphic by the actual original affine coordinate maps. The
already proved genuine product reduction consequently identifies their
original rational Chen spaces in every degree at least two. No affine
decone identification, product decomposition or Chen comparison is an input.
Resonance-component comparison is a separate subsequent obligation.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (hcentral : ∀ i, A.offset i = 0) (i₀ : ι)
local instance centralDeconeComplementDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The actual decone point included in the original slice complement. -/
def actualDeconeToCentralSlice
    (x : (A.actualCentralDecone hcentral i₀).Complement) :
    A.CentralSliceComplement i₀ :=
  ⟨A.actualCentralDeconeEmbedding i₀ x.val, by
    constructor
    · exact A.actualCentralDeconeEmbedding_normal i₀ x.val
    · intro H
      by_cases hH : H = i₀
      · subst H
        rw [A.actualCentralDeconeEmbedding_normal i₀ x.val]
        exact one_ne_zero
      · intro hz
        apply x.property ⟨H, hH⟩
        exact (A.actualCentralDeconeEquation_iff i₀ ⟨H, hH⟩ x.val).mpr hz⟩

/-- The original slice's actual inverse affine coordinate. -/
def actualCentralSliceToDecone (x : A.CentralSliceComplement i₀) :
    (A.actualCentralDecone hcentral i₀).Complement :=
  ⟨A.actualCentralDeconeCoordinate i₀ x.val x.property.1, by
    intro H he
    apply x.property.2 H.val
    have h := (A.actualCentralDeconeEquation_iff i₀ H _).mp he
    rw [A.actualCentralDeconeEmbedding_coordinate i₀ x.val x.property.1] at h
    exact h⟩

@[simp] theorem actualCentralSliceToDecone_deconeToSlice
    (x : (A.actualCentralDecone hcentral i₀).Complement) :
    A.actualCentralSliceToDecone hcentral i₀
      (A.actualDeconeToCentralSlice hcentral i₀ x) = x := by
  apply Subtype.ext
  exact A.actualCentralDeconeCoordinate_embedding i₀ x.val

@[simp] theorem actualDeconeToCentralSlice_sliceToDecone
    (x : A.CentralSliceComplement i₀) :
    A.actualDeconeToCentralSlice hcentral i₀
      (A.actualCentralSliceToDecone hcentral i₀ x) = x := by
  apply Subtype.ext
  exact A.actualCentralDeconeEmbedding_coordinate i₀ x.val x.property.1

theorem actualDeconeToCentralSlice_continuous :
    Continuous (A.actualDeconeToCentralSlice hcentral i₀) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : (A.actualCentralDecone hcentral i₀).Complement =>
    A.actualCentralSliceBase i₀ + A.actualCentralDeconeDirectionMap i₀ x.val)
  exact continuous_const.add
    ((A.actualCentralDeconeDirectionMap i₀).continuous_of_finiteDimensional.comp
      continuous_subtype_val)

theorem actualCentralSliceToDecone_continuous :
    Continuous (A.actualCentralSliceToDecone hcentral i₀) := by
  apply Continuous.subtype_mk
  let shift : A.CentralSliceComplement i₀ → A.ActualCentralSliceDirection i₀ :=
    fun x => ⟨x.val - A.actualCentralSliceBase i₀, by
      change A.normal i₀ (x.val - A.actualCentralSliceBase i₀) = 0
      rw [map_sub, x.property.1, A.actualCentralSliceBase_value, sub_self]⟩
  have hs : Continuous shift := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub continuous_const
  change Continuous (fun x : A.CentralSliceComplement i₀ =>
    A.actualCentralSliceCoordinates i₀ (shift x))
  exact (A.actualCentralSliceCoordinates i₀).toLinearMap.continuous_of_finiteDimensional.comp hs

/-- The genuine affine decone complement is the genuine original slice. -/
def actualDeconeSliceHomeomorph :
    (A.actualCentralDecone hcentral i₀).Complement ≃ₜ A.CentralSliceComplement i₀ where
  toFun := A.actualDeconeToCentralSlice hcentral i₀
  invFun := A.actualCentralSliceToDecone hcentral i₀
  left_inv := A.actualCentralSliceToDecone_deconeToSlice hcentral i₀
  right_inv := A.actualDeconeToCentralSlice_sliceToDecone hcentral i₀
  continuous_toFun := A.actualDeconeToCentralSlice_continuous hcentral i₀
  continuous_invFun := A.actualCentralSliceToDecone_continuous hcentral i₀

/-- The same original central arrangement's true Chen space, reduced to
the constructed affine decone's true original fundamental group. -/
def actualCentralDeconeChenSpaceSuccEquiv (x : A.Complement) (n : ℕ) :
    rationalChenSpace (A.complementGroup x) (n + 1) ≃ₗ[ℚ]
      rationalChenSpace
        (FundamentalGroup (A.actualCentralDecone hcentral i₀).Complement
          (A.actualCentralSliceToDecone hcentral i₀ (A.centralSlicePoint hcentral i₀ x)))
        (n + 1) :=
  (A.centralComplementChenSpaceSuccEquiv hcentral i₀ x n).trans
    (rationalChenSpaceEquiv
      (fundamentalGroupHomeomorphEquiv (A.actualDeconeSliceHomeomorph hcentral i₀).symm
        (A.centralSlicePoint hcentral i₀ x)) (n + 1))

/-- Cardinal ranks preserve the actual original quotient spaces before
any finite-dimensional numerical rank formula is used. -/
theorem actualCentralDeconeChenRank_succ (x : A.Complement) (n : ℕ) :
    A.chenRank x (n + 1) =
      (A.actualCentralDecone hcentral i₀).chenRank
        (A.actualCentralSliceToDecone hcentral i₀ (A.centralSlicePoint hcentral i₀ x))
        (n + 1) :=
  (A.actualCentralDeconeChenSpaceSuccEquiv hcentral i₀ x n).rank_eq

end ChenRanks.AffineArrangement
