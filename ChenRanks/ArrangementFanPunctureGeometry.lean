import ChenRanks.ArrangementFanTriangleBoundary

/-!
# One genuinely constructed fan retains all required puncture geometry

The same actual center supplied by finite affine-subspace avoidance is
used throughout. Its actual finite equation-zero sets, genuine boundary
avoidance, and absence of every double-flat puncture are derived together.
No different choice of centers, finite detector, or regularity premise
is inserted in the resulting factory.
-/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

def actualFanTriangleBadSet (x y z : Fin d → ℂ) : Set (stdSimplex ℝ (Fin 3)) :=
  {p | ∃ H : ι, A.normal H (actualFanTriangleAmbient x y z p) = A.offset H}

theorem actualFanTriangleBadSet_finite_of_actual_center_conditions
    (x y z : A.Complement)
    (hedge : ∀ H : ι, A.normal H z.val - A.normal H x.val ∉
      Submodule.span ℝ ({A.normal H (y.val - x.val)} : Set ℂ))
    (hradial : ∀ H : ι, A.normal H z.val - A.offset H ∉
      Submodule.span ℝ ({A.normal H x.val - A.offset H} : Set ℂ)) :
    (A.actualFanTriangleBadSet x.val y.val z.val).Finite := by
  have hfinite (H : ι) : Set.Finite {p : stdSimplex ℝ (Fin 3) |
      A.normal H (actualFanTriangleAmbient x.val y.val z.val p) = A.offset H} := by
    have hline : (A.normal H z.val - A.offset H) - (A.normal H x.val - A.offset H) ∉
        Submodule.span ℝ ({(A.normal H y.val - A.offset H) -
          (A.normal H x.val - A.offset H)} : Set ℂ) := by
      have hz : (A.normal H z.val - A.offset H) - (A.normal H x.val - A.offset H) =
          A.normal H z.val - A.normal H x.val := by ring
      have hxy : (A.normal H y.val - A.offset H) - (A.normal H x.val - A.offset H) =
          A.normal H (y.val - x.val) := by rw [map_sub]; ring
      rw [hz, hxy]
      exact hedge H
    have h := realFanTriangleEquation_zeroSet_finite
      (A.normal H x.val - A.offset H) (A.normal H y.val - A.offset H)
      (A.normal H z.val - A.offset H) (sub_ne_zero.mpr (x.property H)) hline (hradial H)
    have heq : {p : stdSimplex ℝ (Fin 3) |
        A.normal H (actualFanTriangleAmbient x.val y.val z.val p) = A.offset H} =
        {p : stdSimplex ℝ (Fin 3) | realFanTriangleEquation
          (A.normal H x.val - A.offset H) (A.normal H y.val - A.offset H)
          (A.normal H z.val - A.offset H) p = 0} := by
      ext p
      change A.normal H (actualFanTriangleAmbient x.val y.val z.val p) = A.offset H ↔
        realFanTriangleEquation (A.normal H x.val - A.offset H)
          (A.normal H y.val - A.offset H) (A.normal H z.val - A.offset H) p = 0
      rw [← sub_eq_zero, actualFanTriangleAmbient_equation]
    rwa [← heq] at h
  have hu := Set.finite_iUnion hfinite
  have heq : A.actualFanTriangleBadSet x.val y.val z.val =
      ⋃ H : ι, {p : stdSimplex ℝ (Fin 3) |
        A.normal H (actualFanTriangleAmbient x.val y.val z.val p) = A.offset H} := by
    ext p
    simp only [actualFanTriangleBadSet, Set.mem_setOf_eq, Set.mem_iUnion]
  rwa [← heq] at hu

variable {κ : Type*} [Fintype κ]

/-- Actual straight original edges alone suffice to construct a whole
finite fan whose actual punctures all lie in genuine single-H regular
loci and whose original boundary lies in the original complement. -/
theorem exists_actual_fan_triangle_puncture_geometry
    (x y : κ → A.Complement)
    (hedges : ∀ (j : κ) (t : I) (H : ι),
      A.normal H (actualComplexLinePoint (x j).val (y j).val t) ≠ A.offset H) :
    ∃ z : A.Complement, ∀ j : κ,
      (A.actualFanTriangleBadSet (x j).val (y j).val z.val).Finite ∧
      (∀ (i : Fin 3) (t : I) (H : ι), A.normal H
        (actualFanTriangleAmbient (x j).val (y j).val z.val
          (SingularCohomology.realTriangleFacePath i t)) ≠ A.offset H) ∧
      (∀ p ∈ A.actualFanTriangleBadSet (x j).val (y j).val z.val,
        ∃ H : ι, A.normal H (actualFanTriangleAmbient (x j).val (y j).val z.val p) = A.offset H ∧
          ∀ K : ι, K ≠ H → A.normal K
            (actualFanTriangleAmbient (x j).val (y j).val z.val p) ≠ A.offset K) := by
  obtain ⟨z, hlines, hdoubles⟩ := A.exists_actual_transverse_complement_fan_center x y
  refine ⟨z, ?_⟩
  intro j
  have hb := A.actualFanTriangle_boundary_mem_complement (x j) (y j) z
    (fun H => (hlines H j).2.1) (fun H => (hlines H j).2.2) (hedges j)
  refine ⟨A.actualFanTriangleBadSet_finite_of_actual_center_conditions (x j) (y j) z
    (fun H => (hlines H j).1) (fun H => (hlines H j).2.1), hb, ?_⟩
  intro p hp
  obtain ⟨H, hH⟩ := hp
  refine ⟨H, hH, ?_⟩
  intro K hKH hK
  have hboundary : ∀ (i : Fin 3) (t : I), SingularCohomology.realTriangleFacePath i t ∉
      A.actualFanTriangleBadSet (x j).val (y j).val z.val := by
    intro i t hbad
    obtain ⟨L, hL⟩ := hbad
    exact hb i t L hL
  have hpbad : p ∈ A.actualFanTriangleBadSet (x j).val (y j).val z.val := ⟨H, hH⟩
  have hp0 := realTrianglePoint_coordinates_positive_of_boundary_avoidance _ hboundary p hpbad 0
  have hsum : p 0 + p 1 + p 2 = 1 := by
    have hs := p.property.2
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change p 0 + (p 1 + p 2) = 1 at hs
    linarith
  apply hdoubles H K (Ne.symm hKH) j (p 0) (p 1) (p 2) hp0.ne' hsum
  rw [← actualFanTriangleAmbient_eq_real_sum]
  exact ⟨hH, hK⟩

end ChenRanks.AffineArrangement
