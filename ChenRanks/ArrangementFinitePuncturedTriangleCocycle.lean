import ChenRanks.SingularPartialTriangleBoundaryLoop
import ChenRanks.ArrangementInnerTubeCocycleDetection
import ChenRanks.RealTriangleAffineMetricControl

/-!
# Genuine finite-puncture induction for original arrangement triangles

The bad set is the actual preimage of the original hyperplanes. Every
selected actual puncture lies on exactly one original hyperplane, so
the original canonical-meridian hypothesis derives its local detector.
Continuity constructs a genuine nearby inner triangle. Actual six-strip
maps exclude that puncture, have strictly smaller actual bad-cardinals,
and have safe actual boundaries. Native oriented-edge cancellation then
closes the strong induction. No finite-puncture filling, local detector,
strip vanishing, or removal construction is a premise of the theorem.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

abbrev actualComplementSet : Set (Fin d → ℂ) :=
  {x | ∀ H : ι, A.normal H x ≠ A.offset H}

def actualContinuousTriangleBadSet (F : C(stdSimplex ℝ (Fin 3), Fin d → ℂ)) :
    Set (stdSimplex ℝ (Fin 3)) :=
  {p | ∃ H : ι, A.normal H (F p) = A.offset H}

theorem actualContinuousTriangle_good_iff_not_bad
    (F : C(stdSimplex ℝ (Fin 3), Fin d → ℂ)) (p : stdSimplex ℝ (Fin 3)) :
    F p ∈ A.actualComplementSet ↔ p ∉ A.actualContinuousTriangleBadSet F := by
  classical
  simp only [actualComplementSet, actualContinuousTriangleBadSet, Set.mem_setOf_eq,
    not_exists]

theorem actualContinuousTriangleBadSet_comp
    (F : C(stdSimplex ℝ (Fin 3), Fin d → ℂ))
    (G : C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 3))) :
    A.actualContinuousTriangleBadSet (F.comp G) = G ⁻¹' A.actualContinuousTriangleBadSet F := by
  ext p
  rfl

variable (k : Type) [Field k]

private theorem finitePuncturedTriangle_strongInduction
    (β : cochains k A.Complement 1) (hβ : differential k A.Complement 1 β = 0)
    (hcanonical : ∀ H : ι, values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H (A.actualMeridianDisk H))) = 0)
    (n : ℕ) :
    ∀ (F : C(stdSimplex ℝ (Fin 3), Fin d → ℂ)),
      (A.actualContinuousTriangleBadSet F).ncard = n →
      (A.actualContinuousTriangleBadSet F).Finite →
      ∀ (hboundary : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ A.actualComplementSet),
      (∀ p ∈ A.actualContinuousTriangleBadSet F, ∃ H : ι,
        A.normal H (F p) = A.offset H ∧
          ∀ K : ι, K ≠ H → A.normal K (F p) ≠ A.offset K) →
      partialTriangleBoundaryValue (Fin d → ℂ) A.actualComplementSet k β F hboundary = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn hfinite hboundary hregular
    by_cases hempty : A.actualContinuousTriangleBadSet F = ∅
    · apply partialTriangleBoundaryValue_eq_zero_of_whole_triangle
        (Fin d → ℂ) A.actualComplementSet k β hβ F hboundary
      intro p
      apply (A.actualContinuousTriangle_good_iff_not_bad F p).mpr
      rw [hempty]
      simp
    · obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨H, hH, hothers⟩ := hregular p hp
      let w : A.HyperplaneRegularLocus H := ⟨F p, hH, hothers⟩
      obtain ⟨ε, hε, hdetector⟩ :=
        A.exists_actual_innerTube_closedCochain_detector k H w β hβ (hcanonical H)
      obtain ⟨δ, hδ, hcontrol⟩ :=
        exists_planeRadius_controlling_actual_innerTriangle F p ε hε
      have hbadBoundary : ∀ (i : Fin 3) (t : I),
          realTriangleFacePath i t ∉ A.actualContinuousTriangleBadSet F := by
        intro i t
        exact (A.actualContinuousTriangle_good_iff_not_bad F _).mp (hboundary i t)
      obtain ⟨a, _, hnearVertices, hstripAvoid, hinnerAvoid, hsmaller⟩ :=
        exists_actual_realTriangle_puncture_removal_geometry
          (A.actualContinuousTriangleBadSet F) hfinite hbadBoundary p hp δ hδ
      have hstripBoundary (i : Fin 6) : ∀ (r : Fin 3) (t : I),
          (F.comp (realTriangleAffineMap (realTriangleSixStripVertices a i)))
            (realTriangleFacePath r t) ∈ A.actualComplementSet := by
        intro r t
        exact (A.actualContinuousTriangle_good_iff_not_bad F _).mpr (hstripAvoid i r t)
      have hinnerBoundary : ∀ (r : Fin 3) (t : I),
          (F.comp (realTriangleAffineMap a)) (realTriangleFacePath r t) ∈ A.actualComplementSet := by
        intro r t
        exact (A.actualContinuousTriangle_good_iff_not_bad F _).mpr (hinnerAvoid r t)
      have hstripZero (i : Fin 6) : partialTriangleBoundaryValue
          (Fin d → ℂ) A.actualComplementSet k β
          (F.comp (realTriangleAffineMap (realTriangleSixStripVertices a i)))
          (hstripBoundary i) = 0 := by
        let G := realTriangleAffineMap (realTriangleSixStripVertices a i)
        have hf : (A.actualContinuousTriangleBadSet (F.comp G)).Finite := by
          rw [A.actualContinuousTriangleBadSet_comp]
          exact (hsmaller i).2.2.1
        have hc : (A.actualContinuousTriangleBadSet (F.comp G)).ncard < n := by
          rw [A.actualContinuousTriangleBadSet_comp, ← hn]
          exact (hsmaller i).2.2.2
        apply ih (A.actualContinuousTriangleBadSet (F.comp G)).ncard hc (F.comp G) rfl hf
          (hstripBoundary i)
        intro q hq
        exact hregular (G q) hq
      have hinnerZero : partialTriangleBoundaryValue (Fin d → ℂ) A.actualComplementSet k β
          (F.comp (realTriangleAffineMap a)) hinnerBoundary = 0 := by
        apply partialTriangleBoundaryValue_eq_zero_of_tube_detector
          (Fin d → ℂ) A.actualComplementSet k β hβ w.val ε hdetector
          (F.comp (realTriangleAffineMap a)) hinnerBoundary
        intro q
        exact hcontrol a hnearVertices q
      have hboundaryEqual := partialTriangleSixStrips_originalBoundary_eq_innerBoundary
        (Fin d → ℂ) A.actualComplementSet k β hβ F hboundary a
        hstripBoundary hinnerBoundary hstripZero
      exact hboundaryEqual.trans hinnerZero

/-- Genuine original finite punctures are removed by actual geometric
induction. The only cochain hypotheses are closure and its actual
canonical-meridian values. The actual triangle regularity is a geometric
condition discharged by the original simultaneous fan construction. -/
theorem normalized_closedOne_finite_punctured_triangle_boundary_eq_zero
    (β : cochains k A.Complement 1) (hβ : differential k A.Complement 1 β = 0)
    (hcanonical : ∀ H : ι, values k A.Complement 1 β
      (simplexOfPath A.Complement (A.meridianDiskPathMap H (A.actualMeridianDisk H))) = 0)
    (F : C(stdSimplex ℝ (Fin 3), Fin d → ℂ))
    (hfinite : (A.actualContinuousTriangleBadSet F).Finite)
    (hboundary : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ A.actualComplementSet)
    (hregular : ∀ p ∈ A.actualContinuousTriangleBadSet F, ∃ H : ι,
      A.normal H (F p) = A.offset H ∧
        ∀ K : ι, K ≠ H → A.normal K (F p) ≠ A.offset K) :
    partialTriangleBoundaryValue (Fin d → ℂ) A.actualComplementSet k β F hboundary = 0 :=
  finitePuncturedTriangle_strongInduction A k β hβ hcanonical
    (A.actualContinuousTriangleBadSet F).ncard F rfl hfinite hboundary hregular

end ChenRanks.AffineArrangement
