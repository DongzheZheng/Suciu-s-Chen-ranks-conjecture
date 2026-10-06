import ChenRanks.ArrangementNonparallelNormalPair
import ChenRanks.ArrangementSingleNormalRealMap
import ChenRanks.ArrangementParallelRelations
import ChenRanks.AffineFanCenterConstruction

/-! An actual original complement fan center is constructed for any
finite collection of original edges. All its triangle points with
nonzero center weight avoid every genuine double hyperplane
intersection. Parallel distinct pairs are treated by their actual
nonzero affine discrepancy, rather than a fictitious codimension-four
flat. No general-position center is assumed. -/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Genuine nonproportional original normal pairs. -/
def ActualNonparallelPair :=
  {p : ι × ι // ∀ c : ℂ, A.normal p.2 ≠ c • A.normal p.1}

instance : Fintype A.ActualNonparallelPair := by
  classical
  unfold ActualNonparallelPair
  infer_instance

/-- An actual point of the original nonparallel pair intersection,
constructed by the true surjective normal-pair map. -/
def actualPairFlatPoint (p : A.ActualNonparallelPair) : Fin d → ℂ :=
  (A.actualNormalPairRealMap_surjective p.val.1 p.val.2 p.property
    (A.offset p.val.1, A.offset p.val.2)).choose

theorem actualPairFlatPoint_values (p : A.ActualNonparallelPair) :
    A.actualNormalPairRealMap p.val.1 p.val.2 (A.actualPairFlatPoint p) =
      (A.offset p.val.1, A.offset p.val.2) :=
  (A.actualNormalPairRealMap_surjective p.val.1 p.val.2 p.property
    (A.offset p.val.1, A.offset p.val.2)).choose_spec

/-- Original distinguished-hyperplane point from the already proved
actual meridian-center construction. -/
def actualSingleFlatPoint (H : ι) : Fin d → ℂ :=
  (A.exists_actual_meridian_center H).choose

theorem actualSingleFlatPoint_value (H : ι) :
    A.normal H (A.actualSingleFlatPoint H) = A.offset H :=
  (A.exists_actual_meridian_center H).choose_spec.1

/-- A true original normal kernel is proper, as witnessed by the
actually constructed original normal vector. -/
theorem actualSingleNormalRealKernel_ne_top (H : ι) :
    LinearMap.ker (A.actualSingleNormalRealMap H) ≠ ⊤ := by
  obtain ⟨v, hv⟩ := A.exists_actual_meridian_normal_vector H
  intro htop
  have hmem : v ∈ LinearMap.ker (A.actualSingleNormalRealMap H) := by
    rw [htop]
    exact Submodule.mem_top
  change A.normal H v = 0 at hmem
  rw [hv] at hmem
  exact one_ne_zero hmem

variable {κ : Type*} [Fintype κ]

/-- A genuine complement point simultaneously supplies a fan center
whose actual triangle interiors miss every actual double intersection.
The original edges may be degenerate; no independence of their endpoint
directions or general-position assumption is needed. -/
theorem exists_actual_complement_fan_center (x y : κ → (Fin d → ℂ)) :
    ∃ z : A.Complement, ∀ (H K : ι), H ≠ K → ∀ (j : κ) (r s t : ℝ),
      r ≠ 0 → r + s + t = 1 →
        ¬(A.normal H (r • z.val + s • x j + t • y j) = A.offset H ∧
          A.normal K (r • z.val + s • x j + t • y j) = A.offset K) := by
  classical
  let Λ := (A.ActualNonparallelPair × κ) ⊕ ι
  let base : Λ → (Fin d → ℂ) := Sum.elim
    (fun p => A.actualPairFlatPoint p.1) A.actualSingleFlatPoint
  let bad : Λ → Submodule ℝ (Fin d → ℂ) := Sum.elim
    (fun p => LinearMap.ker (A.actualNormalPairRealMap p.1.val.1 p.1.val.2) ⊔
      Submodule.span ℝ ({x p.2 - base (Sum.inl p), y p.2 - base (Sum.inl p)} :
        Set (Fin d → ℂ)))
    (fun H => LinearMap.ker (A.actualSingleNormalRealMap H))
  have hbad : ∀ l : Λ, bad l ≠ ⊤ := by
    intro l
    rcases l with p | H
    · apply affineFan_badSubmodule_ne_top
      have hdim := A.actualNormalPairRealMap_kernel_finrank
        p.1.val.1 p.1.val.2 p.1.property
      omega
    · exact A.actualSingleNormalRealKernel_ne_top H
  obtain ⟨z, hz⟩ := exists_point_avoiding_finite_affine_subspaces bad base hbad
  have hzComplement : ∀ H : ι, A.normal H z ≠ A.offset H := by
    intro H heq
    apply hz (Sum.inr H)
    change A.normal H (z - A.actualSingleFlatPoint H) = 0
    rw [map_sub, heq, A.actualSingleFlatPoint_value, sub_self]
  refine ⟨⟨z, hzComplement⟩, ?_⟩
  intro H K hHK j r s t hr hsum hmeet
  by_cases hnp : ∀ c : ℂ, A.normal K ≠ c • A.normal H
  · let p : A.ActualNonparallelPair := ⟨(H, K), hnp⟩
    have havoid := affineFan_nonzero_center_weight_avoids_flat
      (LinearMap.ker (A.actualNormalPairRealMap H K)) (A.actualPairFlatPoint p)
      (x j) (y j) z (hz (Sum.inl (p, j))) r s t hr hsum
    apply havoid
    change A.actualNormalPairRealMap H K
      (r • z + s • x j + t • y j - A.actualPairFlatPoint p) = 0
    rw [map_sub]
    have hflat : A.actualNormalPairRealMap H K (A.actualPairFlatPoint p) =
        (A.offset H, A.offset K) := A.actualPairFlatPoint_values p
    rw [hflat]
    apply sub_eq_zero.mpr
    exact Prod.ext hmeet.1 hmeet.2
  · push Not at hnp
    obtain ⟨c, hc⟩ := hnp
    have hδ := A.parallel_offset_discrepancy_ne_zero H K hHK c hc
    apply hδ
    have hvalue := DFunLike.congr_fun hc (r • z + s • x j + t • y j)
    change A.normal K (r • z + s • x j + t • y j) =
      c * A.normal H (r • z + s • x j + t • y j) at hvalue
    rw [hmeet.1, hmeet.2] at hvalue
    exact sub_eq_zero.mpr hvalue.symm

end ChenRanks.AffineArrangement
