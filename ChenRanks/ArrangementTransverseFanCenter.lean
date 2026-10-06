import ChenRanks.ArrangementDoubleIntersectionFanCenter
import ChenRanks.ArrangementSingleNormalRealLines

/-! A genuine original complement fan center simultaneously avoids
actual double flats and the actual one-equation real-line degeneracies.
The three real-line conditions prevent boundary-ray zeros and ensure
nonconstant edge equations have a genuinely two-dimensional affine
triangle image. Equal edge-equation values are retained explicitly. -/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

variable {κ : Type*} [Fintype κ]

/-- The genuine simultaneous center is constructed entirely from the
original arrangement and actual complement edge endpoints. No good
center, transverse intersection, or simple-zero statement is an input. -/
theorem exists_actual_transverse_complement_fan_center
    (x y : κ → A.Complement) :
    ∃ z : A.Complement,
      (∀ (H : ι) (j : κ),
        A.normal H z.val - A.normal H (x j).val ∉
          Submodule.span ℝ ({A.normal H ((y j).val - (x j).val)} : Set ℂ) ∧
        A.normal H z.val - A.offset H ∉
          Submodule.span ℝ ({A.normal H (x j).val - A.offset H} : Set ℂ) ∧
        A.normal H z.val - A.offset H ∉
          Submodule.span ℝ ({A.normal H (y j).val - A.offset H} : Set ℂ)) ∧
      (∀ (H K : ι), H ≠ K → ∀ (j : κ) (r s t : ℝ),
        r ≠ 0 → r + s + t = 1 →
          ¬(A.normal H (r • z.val + s • (x j).val + t • (y j).val) = A.offset H ∧
            A.normal K (r • z.val + s • (x j).val + t • (y j).val) = A.offset K)) := by
  classical
  let LineIndex := ι × κ × Fin 3
  let lineDirection : LineIndex → ℂ := fun p =>
    if p.2.2 = 0 then A.normal p.1 ((y p.2.1).val - (x p.2.1).val)
    else if p.2.2 = 1 then A.normal p.1 (x p.2.1).val - A.offset p.1
    else A.normal p.1 (y p.2.1).val - A.offset p.1
  let lineBase : LineIndex → (Fin d → ℂ) := fun p =>
    if p.2.2 = 0 then (x p.2.1).val else A.actualSingleFlatPoint p.1
  let Λ := (A.ActualNonparallelPair × κ) ⊕ (LineIndex ⊕ ι)
  let base : Λ → (Fin d → ℂ) := Sum.elim
    (fun p => A.actualPairFlatPoint p.1)
    (Sum.elim lineBase A.actualSingleFlatPoint)
  let bad : Λ → Submodule ℝ (Fin d → ℂ) := Sum.elim
    (fun p => LinearMap.ker (A.actualNormalPairRealMap p.1.val.1 p.1.val.2) ⊔
      Submodule.span ℝ ({(x p.2).val - base (Sum.inl p),
        (y p.2).val - base (Sum.inl p)} : Set (Fin d → ℂ)))
    (Sum.elim
      (fun p => (Submodule.span ℝ ({lineDirection p} : Set ℂ)).comap
        (A.actualSingleNormalRealMap p.1))
      (fun H => LinearMap.ker (A.actualSingleNormalRealMap H)))
  have hbad : ∀ l : Λ, bad l ≠ ⊤ := by
    intro l
    rcases l with p | l
    · apply affineFan_badSubmodule_ne_top
      have hdim := A.actualNormalPairRealMap_kernel_finrank
        p.1.val.1 p.1.val.2 p.1.property
      omega
    · rcases l with p | H
      · exact A.actualSingleNormalRealLine_comap_ne_top p.1 (lineDirection p)
      · exact A.actualSingleNormalRealKernel_ne_top H
  obtain ⟨z, hz⟩ := exists_point_avoiding_finite_affine_subspaces bad base hbad
  have hzComplement : ∀ H : ι, A.normal H z ≠ A.offset H := by
    intro H heq
    apply hz (Sum.inr (Sum.inr H))
    change A.normal H (z - A.actualSingleFlatPoint H) = 0
    rw [map_sub, heq, A.actualSingleFlatPoint_value, sub_self]
  refine ⟨⟨z, hzComplement⟩, ?_, ?_⟩
  · intro H j
    constructor
    · have h := hz (Sum.inr (Sum.inl (H, j, 0)))
      change A.normal H (z - (x j).val) ∉
        Submodule.span ℝ ({A.normal H ((y j).val - (x j).val)} : Set ℂ) at h
      simpa only [map_sub] using h
    · constructor
      · have h := hz (Sum.inr (Sum.inl (H, j, 1)))
        change A.normal H (z - A.actualSingleFlatPoint H) ∉
          Submodule.span ℝ ({A.normal H (x j).val - A.offset H} : Set ℂ) at h
        simpa only [map_sub, A.actualSingleFlatPoint_value] using h
      · have h := hz (Sum.inr (Sum.inl (H, j, 2)))
        change A.normal H (z - A.actualSingleFlatPoint H) ∉
          Submodule.span ℝ ({A.normal H (y j).val - A.offset H} : Set ℂ) at h
        simpa only [map_sub, A.actualSingleFlatPoint_value] using h
  · intro H K hHK j r s t hr hsum hmeet
    by_cases hnp : ∀ c : ℂ, A.normal K ≠ c • A.normal H
    · let p : A.ActualNonparallelPair := ⟨(H, K), hnp⟩
      have havoid := affineFan_nonzero_center_weight_avoids_flat
        (LinearMap.ker (A.actualNormalPairRealMap H K)) (A.actualPairFlatPoint p)
        (x j).val (y j).val z (hz (Sum.inl (p, j))) r s t hr hsum
      apply havoid
      change A.actualNormalPairRealMap H K
        (r • z + s • (x j).val + t • (y j).val - A.actualPairFlatPoint p) = 0
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
      have hvalue := DFunLike.congr_fun hc
        (r • z + s • (x j).val + t • (y j).val)
      change A.normal K (r • z + s • (x j).val + t • (y j).val) =
        c * A.normal H (r • z + s • (x j).val + t • (y j).val) at hvalue
      rw [hmeet.1, hmeet.2] at hvalue
      exact sub_eq_zero.mpr hvalue.symm

end ChenRanks.AffineArrangement
