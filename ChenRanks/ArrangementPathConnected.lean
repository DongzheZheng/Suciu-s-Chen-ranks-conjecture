import ChenRanks.ArrangementObjects
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Paths in the original complex affine arrangement complement

For two original complement points, their complex affine line meets each
hyperplane in at most one parameter value unless it misses the hyperplane
entirely. The actual excluded parameter set is finite. Path connectedness
of its complement in the complex plane gives an actual path in the same
arrangement complement. No topological connectedness premise is supplied.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Any two points of the actual complement are joined by an actual path. -/
theorem complement_joined (x y : A.Complement) : Joined x y := by
  classical
  let bad : Set ℂ := {z | ∃ i, A.normal i (x.val +
    z • (y.val - x.val)) = A.offset i}
  have hbad : bad.Finite := by
    apply (Set.finite_range (fun i ↦
      (A.offset i - A.normal i x.val) / A.normal i (y.val - x.val))).subset
    rintro z ⟨i, hi⟩
    have hd : A.normal i (y.val - x.val) ≠ 0 := by
      intro hz
      apply x.property i
      simpa only [map_add, map_smul, hz, smul_eq_mul, mul_zero, add_zero] using hi
    refine ⟨i, (div_eq_iff hd).mpr ?_⟩
    have hi' : A.normal i x.val + z * A.normal i (y.val - x.val) = A.offset i := by
      simpa only [map_add, map_smul, smul_eq_mul] using hi
    linear_combination -hi'
  have h0 : (0 : ℂ) ∈ badᶜ := by
    rintro ⟨i, hi⟩
    exact x.property i (by simpa only [zero_smul, add_zero] using hi)
  have h1 : (1 : ℂ) ∈ badᶜ := by
    rintro ⟨i, hi⟩
    exact y.property i (by simpa only [one_smul, add_sub_cancel] using hi)
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hj := (hbad.countable.isPathConnected_compl_of_one_lt_rank hr).joinedIn 0 h0 1 h1
  let f : (↥(badᶜ)) → A.Complement := fun z ↦
    ⟨x.val + (z : ℂ) • (y.val - x.val),
      fun i hi ↦ z.property ⟨i, hi⟩⟩
  have hf : Continuous f := by
    fun_prop
  have hp : Joined (f ⟨0, h0⟩) (f ⟨1, h1⟩) := ⟨hj.joined_subtype.somePath.map hf⟩
  simpa only [f, zero_smul, add_zero, one_smul, add_sub_cancel] using hp

/-- The original complement is path connected once an original basepoint
is supplied. Existence of a basepoint is not a connectedness hypothesis. -/
theorem complement_pathConnectedSpace (x : A.Complement) : PathConnectedSpace A.Complement :=
  ⟨⟨x⟩, A.complement_joined⟩

end ChenRanks.AffineArrangement
