import ChenRanks.ArrangementPathConnected
import ChenRanks.ArrangementMeridianBasepoint

/-!
# Actual regular-hyperplane paths and actual deletion

The distinguished hyperplane, with all other actual hyperplanes removed,
is a genuine subtype of the original complex affine space. The same
finite-excluded-parameter construction that proves connectivity of the
original complement gives actual paths in this regular locus. The
deleted arrangement and the continuous inclusion into its complement
are constructed from the original equations. No meridian generation or
cohomology spanning assertion is used.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance hyperplaneRegularPathLabelDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The actual regular part of one distinguished original hyperplane. -/
def HyperplaneRegularLocus (H : ι) :=
  {x : Fin d → ℂ // A.normal H x = A.offset H ∧
    ∀ K : ι, K ≠ H → A.normal K x ≠ A.offset K}

instance (H : ι) : TopologicalSpace (A.HyperplaneRegularLocus H) := by
  unfold HyperplaneRegularLocus
  infer_instance

/-- Every regular-hyperplane point is genuinely joined to every other
such point inside the same original regular hyperplane. -/
theorem hyperplaneRegularLocus_joined (H : ι)
    (x y : A.HyperplaneRegularLocus H) : Joined x y := by
  classical
  let bad : Set ℂ := {z | ∃ K : {K : ι // K ≠ H},
    A.normal K.val (x.val + z • (y.val - x.val)) = A.offset K.val}
  have hbad : bad.Finite := by
    apply (Set.finite_range (fun K : {K : ι // K ≠ H} ↦
      (A.offset K.val - A.normal K.val x.val) /
        A.normal K.val (y.val - x.val))).subset
    rintro z ⟨K, hz⟩
    have hd : A.normal K.val (y.val - x.val) ≠ 0 := by
      intro hzero
      apply x.property.2 K.val K.property
      simpa only [map_add, map_smul, hzero, smul_eq_mul,
        mul_zero, add_zero] using hz
    refine ⟨K, (div_eq_iff hd).mpr ?_⟩
    have hz' : A.normal K.val x.val +
        z * A.normal K.val (y.val - x.val) = A.offset K.val := by
      simpa only [map_add, map_smul, smul_eq_mul] using hz
    linear_combination -hz'
  have h0 : (0 : ℂ) ∈ badᶜ := by
    rintro ⟨K, hz⟩
    exact x.property.2 K.val K.property
      (by simpa only [zero_smul, add_zero] using hz)
  have h1 : (1 : ℂ) ∈ badᶜ := by
    rintro ⟨K, hz⟩
    exact y.property.2 K.val K.property
      (by simpa only [one_smul, add_sub_cancel] using hz)
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hj := (hbad.countable.isPathConnected_compl_of_one_lt_rank hr).joinedIn
    0 h0 1 h1
  let f : (↥(badᶜ)) → A.HyperplaneRegularLocus H := fun z ↦
    ⟨x.val + (z : ℂ) • (y.val - x.val), by
      constructor
      · rw [map_add, map_smul, map_sub, x.property.1, y.property.1,
          sub_self, smul_eq_mul, mul_zero, add_zero]
      · intro K hKH hz
        exact z.property ⟨⟨K, hKH⟩, hz⟩⟩
  have hf : Continuous f := by
    fun_prop
  have hp : Joined (f ⟨0, h0⟩) (f ⟨1, h1⟩) :=
    ⟨hj.joined_subtype.somePath.map hf⟩
  have hfx : f ⟨0, h0⟩ = x := by
    apply Subtype.ext
    simp only [f, zero_smul, add_zero]
  have hfy : f ⟨1, h1⟩ = y := by
    apply Subtype.ext
    simp only [f, one_smul, add_sub_cancel]
  rwa [hfx, hfy] at hp

/-- Original distinctness supplies an actual regular-hyperplane point. -/
theorem hyperplaneRegularLocus_nonempty (H : ι) :
    Nonempty (A.HyperplaneRegularLocus H) := by
  obtain ⟨x, hH, hrest⟩ := A.exists_actual_meridian_center H
  exact ⟨⟨x, hH, hrest⟩⟩

/-- The actual regular part of every original hyperplane is path connected. -/
theorem hyperplaneRegularLocus_pathConnectedSpace (H : ι) :
    PathConnectedSpace (A.HyperplaneRegularLocus H) :=
  ⟨A.hyperplaneRegularLocus_nonempty H, A.hyperplaneRegularLocus_joined H⟩

/-- The genuine deletion of one original hyperplane. -/
def deleteHyperplane (H : ι) : AffineArrangement d {K : ι // K ≠ H} where
  normal K := A.normal K.val
  offset K := A.offset K.val
  normal_ne_zero K := A.normal_ne_zero K.val
  distinct K J hKJ := A.distinct (Subtype.coe_injective.ne hKJ)

/-- The same actual point belongs to the actual deleted complement. -/
def hyperplaneRegularToDeletedComplement (H : ι) :
    C(A.HyperplaneRegularLocus H, (A.deleteHyperplane H).Complement) where
  toFun x := ⟨x.val, fun K ↦ x.property.2 K.val K.property⟩
  continuous_toFun := by
    fun_prop

@[simp] theorem hyperplaneRegularToDeletedComplement_val (H : ι)
    (x : A.HyperplaneRegularLocus H) :
    (A.hyperplaneRegularToDeletedComplement H x).val = x.val := rfl

end ChenRanks.AffineArrangement
