import ChenRanks.PhaseGridContinuousLiftUniqueness
import ChenRanks.BasedTwicePuncturedSimplexLift
import ChenRanks.SingularTrianglePathHomotopy

/-!
# Actual restrictions of the based triangle grid filling

The filling is the genuinely constructed based two-simplex lift of the
two original phases. Its first and diagonal edges are the existing
selected path lifts by actual covering uniqueness. Evaluating the first
identity at its terminal vertex derives the genuine first integer
displacement. The second edge is then the actual translate of its
selected path lift. Projection, initial values and integer displacement
are all derived from the original simplex and its genuine lift; no
triangle compatibility, terminal value, or cup vanishing is an input.
-/

noncomputable section

open AlgebraicTopology unitInterval
open ChenRanks.SingularCohomology

namespace ChenRanks

/-- The actual first edge of the actual based filling is the existing
selected lift of the actual original first edge. -/
theorem basedTwicePuncturedTriangle_first_edge_eq_selected
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    (basedTwicePuncturedSimplexGridLift 2 s).comp (realTriangleFacePath 2) =
      (phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 2))).toContinuousMap := by
  apply phaseGridFilling_edge_eq_selected
  · exact basedTwicePuncturedSimplexGridLift_projects 2 s
  · have hzero : realTriangleFacePath 2 0 =
        (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 3)) := by
      simpa using realTriangleFacePath_zero 2
    rw [hzero, basedTwicePuncturedSimplexGridLift_vertex_zero]

/-- The actual diagonal edge of the same actual filling is the selected
lift of the actual original diagonal edge, based at the same vertex. -/
theorem basedTwicePuncturedTriangle_diagonal_edge_eq_selected
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    (basedTwicePuncturedSimplexGridLift 2 s).comp (realTriangleFacePath 1) =
      (phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 1))).toContinuousMap := by
  apply phaseGridFilling_edge_eq_selected
  · exact basedTwicePuncturedSimplexGridLift_projects 2 s
  · have hzero : realTriangleFacePath 1 0 =
        (stdSimplex.vertex 0 : stdSimplex ℝ (Fin 3)) := by
      simpa using realTriangleFacePath_zero 1
    rw [hzero, basedTwicePuncturedSimplexGridLift_vertex_zero]

/-- The actual value of the filling at its second vertex is derived
by evaluating the genuine first-edge lift at its genuine endpoint. -/
theorem basedTwicePuncturedTriangle_vertex_one
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    basedTwicePuncturedSimplexGridLift 2 s (stdSimplex.vertex 1) =
      phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2)))
        (phaseGridPrincipalPoint (s (stdSimplex.vertex 1))) := by
  have h := congrArg (fun γ : C(I, PhaseGridComplement) => γ 1)
    (basedTwicePuncturedTriangle_first_edge_eq_selected s)
  change basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 2 1) =
    phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 2)) 1 at h
  rw [Path.target] at h
  have hone : realTriangleFacePath 2 1 =
      (stdSimplex.vertex 1 : stdSimplex ℝ (Fin 3)) := by
    simpa using realTriangleFacePath_one 2
  change basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 2 1) =
    phaseGridDeckTranslation
      (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2)))
      (phaseGridPrincipalPoint (s (realTriangleFacePath 2 1))) at h
  rw [hone] at h
  exact h

/-- The actual terminal value of the diagonal lift, derived similarly
from the genuine diagonal restriction rather than assumed beforehand. -/
theorem basedTwicePuncturedTriangle_vertex_two
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    basedTwicePuncturedSimplexGridLift 2 s (stdSimplex.vertex 2) =
      phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 1)))
        (phaseGridPrincipalPoint (s (stdSimplex.vertex 2))) := by
  have h := congrArg (fun γ : C(I, PhaseGridComplement) => γ 1)
    (basedTwicePuncturedTriangle_diagonal_edge_eq_selected s)
  change basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 1 1) =
    phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 1)) 1 at h
  rw [Path.target] at h
  have hone : realTriangleFacePath 1 1 =
      (stdSimplex.vertex 2 : stdSimplex ℝ (Fin 3)) := by
    simpa using realTriangleFacePath_one 1
  change basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 1 1) =
    phaseGridDeckTranslation
      (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 1)))
      (phaseGridPrincipalPoint (s (realTriangleFacePath 1 1))) at h
  rw [hone] at h
  exact h

/-- The actual second edge is the actual integer translate required by
the first edge. Its genuine source equality is proved above internally. -/
theorem basedTwicePuncturedTriangle_second_edge_eq_translated_selected
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) :
    (basedTwicePuncturedSimplexGridLift 2 s).comp (realTriangleFacePath 0) =
      ((phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 0))).map
        (phaseGridDeckTranslation
          (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2)))).continuous).toContinuousMap := by
  apply phaseGridFilling_edge_eq_translated_selected
  · exact basedTwicePuncturedSimplexGridLift_projects 2 s
  · have hzero : realTriangleFacePath 0 0 =
        (stdSimplex.vertex 1 : stdSimplex ℝ (Fin 3)) := by
      simpa using realTriangleFacePath_zero 0
    rw [hzero]
    exact basedTwicePuncturedTriangle_vertex_one s

/-- Literal pointwise restriction of the genuine first edge. -/
theorem basedTwicePuncturedTriangle_first_edge_apply
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) (t : I) :
    basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 2 t) =
      phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 2)) t :=
  congrArg (fun γ : C(I, PhaseGridComplement) => γ t)
    (basedTwicePuncturedTriangle_first_edge_eq_selected s)

/-- Literal pointwise restriction of the genuine diagonal edge. -/
theorem basedTwicePuncturedTriangle_diagonal_edge_apply
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) (t : I) :
    basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 1 t) =
      phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 1)) t :=
  congrArg (fun γ : C(I, PhaseGridComplement) => γ t)
    (basedTwicePuncturedTriangle_diagonal_edge_eq_selected s)

/-- Literal pointwise restriction of the genuine translated second
edge, with the actual first integer increment from the original simplex. -/
theorem basedTwicePuncturedTriangle_second_edge_apply
    (s : C(stdSimplex ℝ (Fin 3), TwicePuncturedComplex)) (t : I) :
    basedTwicePuncturedSimplexGridLift 2 s (realTriangleFacePath 0 t) =
      phaseGridDeckTranslation
        (twicePuncturedArgumentDeckIncrement (s.comp (realTriangleFacePath 2)))
        (phaseGridLiftedOriginalPath (s.comp (realTriangleFacePath 0)) t) :=
  congrArg (fun γ : C(I, PhaseGridComplement) => γ t)
    (basedTwicePuncturedTriangle_second_edge_eq_translated_selected s)

end ChenRanks
