import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Actual finite uniform subdivisions of actual continuous paths.
The subdivision and its oscillation bound are constructed from native
Heine--Cantor and the Archimedean property, not supplied as inputs. -/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The actual `n`-step uniform grid in the original unit interval. -/
def uniformUnitGrid (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) : I :=
  ⟨(i.val : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
      exact_mod_cast Nat.le_of_lt_succ i.isLt⟩

@[simp] theorem uniformUnitGrid_zero (n : ℕ) (hn : 0 < n) :
    uniformUnitGrid n hn 0 = 0 := by
  apply Subtype.ext
  simp [uniformUnitGrid]

@[simp] theorem uniformUnitGrid_last (n : ℕ) (hn : 0 < n) :
    uniformUnitGrid n hn (Fin.last n) = 1 := by
  apply Subtype.ext
  simp [uniformUnitGrid, ne_of_gt hn]

/-- Native convex-combination reparametrization of a genuine grid
subinterval is at distance exactly `s/n` from its initial endpoint. -/
theorem uniformUnitGrid_convexCombo_distance (n : ℕ) (hn : 0 < n)
    (i : Fin n) (s : I) :
    dist (Set.Icc.convexCombo (uniformUnitGrid n hn i.castSucc)
      (uniformUnitGrid n hn i.succ) s) (uniformUnitGrid n hn i.castSucc) =
        (s : ℝ) / n := by
  change |((1 - (s : ℝ)) * ((i.val : ℝ) / n) +
    (s : ℝ) * (((i.val + 1 : ℕ) : ℝ) / n)) - ((i.val : ℝ) / n)| =
      (s : ℝ) / n
  have h : (1 - (s : ℝ)) * ((i.val : ℝ) / n) +
      (s : ℝ) * (((i.val + 1 : ℕ) : ℝ) / n) - ((i.val : ℝ) / n) =
        (s : ℝ) / n := by
    push_cast
    ring
  rw [h, abs_of_nonneg (div_nonneg s.property.1 (Nat.cast_nonneg n))]

/-- Any actual continuous path has a genuine finite uniform grid on
which every native subpath remains within any prescribed positive
metric radius of its actual initial endpoint. -/
theorem exists_uniformUnitGrid_path_oscillation {X : Type*} [PseudoMetricSpace X]
    (γ : C(I, X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (hn : 0 < n), ∀ (i : Fin n) (s : I),
      dist (γ (Set.Icc.convexCombo (uniformUnitGrid n hn i.castSucc)
        (uniformUnitGrid n hn i.succ) s)) (γ (uniformUnitGrid n hn i.castSucc)) < ε := by
  have hu : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  intro i s
  apply hbound
  rw [uniformUnitGrid_convexCombo_distance]
  have hstep : 1 / ((m + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  exact (div_le_div_of_nonneg_right s.property.2 (by positivity)).trans_lt hstep

end ChenRanks
