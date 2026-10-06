import ChenRanks.SingularFirstCohomologyLoopDetection
import ChenRanks.SingularSquareCocycleHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Actual singular first cohomology and actual based loop characters

Evaluation descends through the original quotient of based paths by
fixed-endpoint homotopy. Genuine concatenation triangles prove the
character law. The native fundamental group multiplies endomorphisms
in the reverse order to path concatenation; commutativity of the actual
coefficient additive group accounts for this order explicitly.

The final injectivity assertion uses genuine conjugated original loops
and the proved all-loop detection of native singular H¹. No Hurewicz,
classifying map, character equivalence, or H² injection is an input.
-/

noncomputable section

open unitInterval CategoryTheory

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] (k : Type) [Field k]

/-- The actual class functional agrees on genuinely homotopic based loops. -/
theorem closedPathEvaluation_eq_of_based_homotopy (base : X)
    {p q : Path base base} (H : p.Homotopy q) :
    closedPathEvaluation k X p.toContinuousMap (by simp) =
      closedPathEvaluation k X q.toContinuousMap (by simp) := by
  let F : C(I × I, X) :=
    ⟨fun z => H (z.2, z.1), H.continuous.comp continuous_swap⟩
  have hv : ∀ s : I, F (1, s) = F (0, s) := by
    intro s
    change H (s, 1) = H (s, 0)
    rw [Path.Homotopy.target, Path.Homotopy.source]
  have hb : squareBottomPath X F = p.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact H.toHomotopy.apply_zero t
  have ht : squareTopPath X F = q.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact H.toHomotopy.apply_one t
  apply LinearMap.ext
  intro h
  have he := closedPathEvaluation_squareBottom_eq_top X k F hv h
  simpa only [hb, ht] using he

/-- Actual loop evaluation, as a linear functional on actual singular H¹,
descended through the actual based fundamental-group quotient. -/
def basedLoopClassEvaluation (base : X) (g : FundamentalGroup X base) :
    cohomology k X 1 →ₗ[k] k :=
  Quotient.lift
    (fun p : Path base base => closedPathEvaluation k X p.toContinuousMap (by simp))
    (by
      intro p q hpq
      obtain ⟨H⟩ := hpq
      exact closedPathEvaluation_eq_of_based_homotopy X k base H)
    g.toPath

@[simp]
theorem basedLoopClassEvaluation_mk (base : X) (p : Path base base) :
    basedLoopClassEvaluation X k base (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      closedPathEvaluation k X p.toContinuousMap (by simp) := rfl

private theorem basedLoopClassEvaluation_trans (base : X)
    (g h : Path.Homotopic.Quotient base base) (a : cohomology k X 1) :
    basedLoopClassEvaluation X k base (FundamentalGroup.fromPath (g.trans h)) a =
      basedLoopClassEvaluation X k base (FundamentalGroup.fromPath g) a +
        basedLoopClassEvaluation X k base (FundamentalGroup.fromPath h) a := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction h using Path.Homotopic.Quotient.ind with
    | mk q =>
      obtain ⟨b, rfl⟩ := cocycleClass_surjective k X 1 a
      change closedPathEvaluation k X (p.trans q).toContinuousMap (by simp)
          (cocycleClass k X 1 b) =
        closedPathEvaluation k X p.toContinuousMap (by simp) (cocycleClass k X 1 b) +
          closedPathEvaluation k X q.toContinuousMap (by simp) (cocycleClass k X 1 b)
      simp only [closedPathEvaluation_cocycleClass]
      exact actualPathCochainValue_trans k X (cocycleCochain k X 1 b)
        (cocycleCochain_closed k X 1 b) p q

private theorem basedLoopClassEvaluation_one (base : X) (a : cohomology k X 1) :
    basedLoopClassEvaluation X k base 1 a = 0 := by
  have h := basedLoopClassEvaluation_trans X k base
    (FundamentalGroup.toPath (1 : FundamentalGroup X base))
    (FundamentalGroup.toPath (1 : FundamentalGroup X base)) a
  change basedLoopClassEvaluation X k base (1 * 1) a =
    basedLoopClassEvaluation X k base 1 a + basedLoopClassEvaluation X k base 1 a at h
  rw [one_mul] at h
  linear_combination -h

private theorem basedLoopClassEvaluation_mul (base : X)
    (g h : FundamentalGroup X base) (a : cohomology k X 1) :
    basedLoopClassEvaluation X k base (g * h) a =
      basedLoopClassEvaluation X k base g a + basedLoopClassEvaluation X k base h a := by
  change basedLoopClassEvaluation X k base
      (FundamentalGroup.fromPath (h.toPath.trans g.toPath)) a = _
  rw [basedLoopClassEvaluation_trans]
  exact add_comm _ _

/-- Actual singular H¹ evaluated on native homotopy classes is a genuine
additive character of the original based fundamental group. -/
def firstCohomologyCharacter (base : X) (a : cohomology k X 1) :
    Additive (FundamentalGroup X base) →+ k where
  toFun g := basedLoopClassEvaluation X k base g.toMul a
  map_zero' := basedLoopClassEvaluation_one X k base a
  map_add' g h := basedLoopClassEvaluation_mul X k base g.toMul h.toMul a

@[simp]
theorem firstCohomologyCharacter_mk (base : X) (a : cohomology k X 1)
    (p : Path base base) :
    firstCohomologyCharacter X k base a
        (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) =
      closedPathEvaluation k X p.toContinuousMap (by simp) a := rfl

/-- The native first-cohomology-to-character map is genuinely k-linear. -/
def firstCohomologyToCharacters (base : X) :
    cohomology k X 1 →ₗ[k] (Additive (FundamentalGroup X base) →+ k) where
  toFun a := firstCohomologyCharacter X k base a
  map_add' a b := by
    ext g
    exact (basedLoopClassEvaluation X k base g).map_add a b
  map_smul' c a := by
    ext g
    exact (basedLoopClassEvaluation X k base g).map_smul c a

/-- Based-loop evaluation zero implies all original free-loop values
zero, by actual path concatenation with a path to the original basepoint. -/
theorem firstCohomologyToCharacters_eq_zero_iff [PathConnectedSpace X]
    (base : X) (a : cohomology k X 1) :
    firstCohomologyToCharacters X k base a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    obtain ⟨b, rfl⟩ := cocycleClass_surjective k X 1 a
    apply (cocycleClass_eq_zero_iff_closed_path_values X k b).mpr
    intro γ hγ
    let p : Path (γ 0) (γ 0) := ⟨γ, rfl, hγ.symm⟩
    let px := PathConnectedSpace.somePath base (γ 0)
    have hbased : ∀ q : Path base base,
        actualPathCochainValue k X (cocycleCochain k X 1 b) q = 0 := by
      intro q
      have hq := congrArg
        (fun f : Additive (FundamentalGroup X base) →+ k =>
          f (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)))) ha
      change firstCohomologyCharacter X k base (cocycleClass k X 1 b)
          (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q))) = 0 at hq
      rw [firstCohomologyCharacter_mk, closedPathEvaluation_cocycleClass] at hq
      exact hq
    have hloop := hbased ((px.trans p).trans px.symm)
    have hcancel := hbased (px.trans px.symm)
    rw [actualPathCochainValue_trans k X _ (cocycleCochain_closed k X 1 b),
      actualPathCochainValue_trans k X _ (cocycleCochain_closed k X 1 b)] at hloop
    rw [actualPathCochainValue_trans k X _ (cocycleCochain_closed k X 1 b)] at hcancel
    change actualPathCochainValue k X (cocycleCochain k X 1 b) p = 0
    linear_combination hloop - hcancel
  · intro ha
    rw [ha, map_zero]

/-- The actual H¹-to-character map is injective. Surjectivity and the
native group-bar H² cup comparison are separate remaining constructions. -/
theorem firstCohomologyToCharacters_injective [PathConnectedSpace X] (base : X) :
    Function.Injective (firstCohomologyToCharacters X k base) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (firstCohomologyToCharacters_eq_zero_iff X k base (a - b)).mp
  rw [map_sub, hab, sub_self]

end ChenRanks.SingularCohomology
