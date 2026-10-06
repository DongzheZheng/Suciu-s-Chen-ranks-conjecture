import ChenRanks.SingularPartialTriangleSixStripCancellation
import ChenRanks.SingularPathCocycleAdditivity

/-!
# A genuine closed boundary loop of an actual partial triangle

The actual three subspace-valued native faces give actual paths with
matching endpoints. Their concatenation is a true closed path. Native
concatenation and reversal identify its value with the negative of the
literal partial-triangle boundary. Thus an actual local closed-loop
detector applies to a triangle lying in its actual metric tube.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (V : Type) [TopologicalSpace V] (U : Set V)

theorem partialTriangleVertex_mem
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (i : Fin 3) : F (stdSimplex.vertex i) ∈ U := by
  fin_cases i
  · simpa [realTriangleFacePath_zero, Fin.succAbove] using hF 2 0
  · simpa [realTriangleFacePath_one, Fin.succAbove] using hF 2 1
  · simpa [realTriangleFacePath_one, Fin.succAbove] using hF 0 1

def partialTriangleActualVertex (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (i : Fin 3) : U :=
  ⟨F (stdSimplex.vertex i), partialTriangleVertex_mem V U F hF i⟩

def partialTriangleBoundaryActualPath (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (i : Fin 3) :
    Path (partialTriangleActualVertex V U F hF (i.succAbove 0))
      (partialTriangleActualVertex V U F hF (i.succAbove 1)) where
  toContinuousMap := partialTriangleFacePath V U F hF i
  source' := by
    apply Subtype.ext
    change F (realTriangleFacePath i 0) = F (stdSimplex.vertex (i.succAbove 0))
    rw [realTriangleFacePath_zero]
  target' := by
    apply Subtype.ext
    change F (realTriangleFacePath i 1) = F (stdSimplex.vertex (i.succAbove 1))
    rw [realTriangleFacePath_one]

def partialTriangleActualBoundaryLoop
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U) :
    Path (partialTriangleActualVertex V U F hF 0) (partialTriangleActualVertex V U F hF 0) :=
  ((partialTriangleBoundaryActualPath V U F hF 2).trans
    (partialTriangleBoundaryActualPath V U F hF 0)).trans
      (partialTriangleBoundaryActualPath V U F hF 1).symm

variable (k : Type) [Field k]

theorem partialTriangleActualBoundaryLoop_value
    (β : cochains k U 1) (hβ : differential k U 1 β = 0)
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U) :
    actualPathCochainValue k U β (partialTriangleActualBoundaryLoop V U F hF) =
      -partialTriangleBoundaryValue V U k β F hF := by
  let p := partialTriangleBoundaryActualPath V U F hF 2
  let q := partialTriangleBoundaryActualPath V U F hF 0
  let r := partialTriangleBoundaryActualPath V U F hF 1
  have heq : r.symm.toContinuousMap = actualReversedContinuousPath r.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    rfl
  have hr := closedOne_reversed_path_value k U β hβ r.toContinuousMap
  rw [← heq] at hr
  change actualPathCochainValue k U β r.symm = -actualPathCochainValue k U β r at hr
  change actualPathCochainValue k U β ((p.trans q).trans r.symm) = _
  rw [actualPathCochainValue_trans k U β hβ, actualPathCochainValue_trans k U β hβ]
  unfold actualPathCochainValue at hr ⊢
  rw [hr]
  unfold partialTriangleBoundaryValue
  have hpmap : p.toContinuousMap = partialTriangleFacePath V U F hF 2 := rfl
  have hqmap : q.toContinuousMap = partialTriangleFacePath V U F hF 0 := rfl
  have hrmap : r.toContinuousMap = partialTriangleFacePath V U F hF 1 := rfl
  rw [hpmap, hqmap, hrmap]
  ring

private theorem path_trans_property {X : Type} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) (P : X → Prop)
    (hp : ∀ t : I, P (p t)) (hq : ∀ t : I, P (q t)) :
    ∀ t : I, P (p.trans q t) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

/-- This intermediate local theorem consumes an actual metric-tube
loop detector. The arrangement application derives that detector from
its actual canonical meridian and its actual finite equations. -/
theorem partialTriangleBoundaryValue_eq_zero_of_tube_detector
    [PseudoMetricSpace V] (β : cochains k U 1) (hβ : differential k U 1 β = 0)
    (w : V) (ε : ℝ)
    (hdetector : ∀ γ : C(I, U), γ 0 = γ 1 →
      (∀ t : I, dist (γ t).val w < ε) → values k U 1 β (simplexOfPath U γ) = 0)
    (F : C(stdSimplex ℝ (Fin 3), V))
    (hF : ∀ (i : Fin 3) (t : I), F (realTriangleFacePath i t) ∈ U)
    (hnear : ∀ p : stdSimplex ℝ (Fin 3), dist (F p) w < ε) :
    partialTriangleBoundaryValue V U k β F hF = 0 := by
  let p := partialTriangleBoundaryActualPath V U F hF 2
  let q := partialTriangleBoundaryActualPath V U F hF 0
  let r := partialTriangleBoundaryActualPath V U F hF 1
  have hp : ∀ t : I, dist (p t).val w < ε := fun t => hnear (realTriangleFacePath 2 t)
  have hq : ∀ t : I, dist (q t).val w < ε := fun t => hnear (realTriangleFacePath 0 t)
  have hr : ∀ t : I, dist (r.symm t).val w < ε := by
    intro t
    exact hnear (realTriangleFacePath 1 (unitInterval.symm t))
  have hloopNear := path_trans_property (p.trans q) r.symm
    (fun x : U => dist x.val w < ε)
    (path_trans_property p q (fun x : U => dist x.val w < ε) hp hq) hr
  have hzero := hdetector (partialTriangleActualBoundaryLoop V U F hF).toContinuousMap
    (by change (partialTriangleActualBoundaryLoop V U F hF) 0 =
      (partialTriangleActualBoundaryLoop V U F hF) 1; simp) hloopNear
  have hvalue := partialTriangleActualBoundaryLoop_value V U k β hβ F hF
  change actualPathCochainValue k U β (partialTriangleActualBoundaryLoop V U F hF) = 0 at hzero
  linear_combination hvalue - hzero

end ChenRanks.SingularCohomology
