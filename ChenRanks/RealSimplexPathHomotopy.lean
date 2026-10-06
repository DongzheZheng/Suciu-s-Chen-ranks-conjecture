import ChenRanks.CircleSimplexArgumentLift
import Mathlib.Topology.Homotopy.Path

/-!
# A genuine fixed-endpoint homotopy inside the original real simplex

Actual convex interpolation gives a native path homotopy between any
two original paths with the same endpoints. No simple-connectedness,
path-homotopy comparison, or singular homology premise is supplied.
-/

noncomputable section

open unitInterval

namespace ChenRanks

def realSimplexPathHomotopy (n : ℕ)
    {x y : stdSimplex ℝ (Fin (n + 1))} (p q : Path x y) : p.Homotopy q where
  toFun z := ⟨(1 - (z.1 : ℝ)) • (p z.2).val + (z.1 : ℝ) • (q z.2).val,
    (convex_stdSimplex ℝ (Fin (n + 1))) (p z.2).property (q z.2).property
      (sub_nonneg.mpr z.1.property.2) z.1.property.1
      (sub_add_cancel 1 (z.1 : ℝ))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hp : Continuous (fun z : I × I => (p z.2).val) :=
      continuous_subtype_val.comp (p.continuous.comp continuous_snd)
    have hq : Continuous (fun z : I × I => (q z.2).val) :=
      continuous_subtype_val.comp (q.continuous.comp continuous_snd)
    have hs : Continuous (fun z : I × I => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hs).smul hp).add (hs.smul hq)
  map_zero_left t := by
    apply Subtype.ext
    simp
  map_one_left t := by
    apply Subtype.ext
    simp
  prop' s t ht := by
    rcases ht with rfl | rfl
    · apply Subtype.ext
      change (1 - (s : ℝ)) • (p 0).val + (s : ℝ) • (q 0).val = (p 0).val
      rw [Path.source, Path.source]
      rw [← add_smul, sub_add_cancel, one_smul]
    · apply Subtype.ext
      change (1 - (s : ℝ)) • (p 1).val + (s : ℝ) • (q 1).val = (p 1).val
      rw [Path.target, Path.target]
      rw [← add_smul, sub_add_cancel, one_smul]

end ChenRanks
