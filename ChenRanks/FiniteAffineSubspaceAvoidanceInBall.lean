import ChenRanks.FiniteAffineSubspaceAvoidance
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Actual nearby points avoiding finitely many real affine subspaces

The algebraic finite-avoidance theorem constructs a direction outside
all the actual proper subspaces. Each actual translate then excludes
at most one real line parameter. Density of the actual finite-set
complement supplies a parameter in a derived small interval. This
constructs an avoiding point in any actual positive-radius ball,
including empty families and zero-dimensional ambient spaces.
-/

noncomputable section

namespace ChenRanks

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Properness, rather than a general-position premise, constructs
an actual avoiding point arbitrarily close to any actual center. -/
theorem exists_point_avoiding_finite_affine_subspaces_in_ball
    (S : ι → Submodule ℝ V) (a : ι → V) (hS : ∀ i, S i ≠ ⊤)
    (x : V) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : V, dist z x < ε ∧ ∀ i, z - a i ∉ S i := by
  classical
  obtain ⟨v, hv⟩ := exists_point_avoiding_finite_affine_subspaces S
    (fun _ => 0) hS
  have hv' : ∀ i, v ∉ S i := by
    intro i
    simpa only [sub_zero] using hv i
  let bad : Set ℝ := {t | ∃ i, x + t • v - a i ∈ S i}
  have hsingle : ∀ i, ({t : ℝ | x + t • v - a i ∈ S i} : Set ℝ).Subsingleton := by
    intro i t ht s hs
    by_contra hts
    have hdiff : (t - s) • v ∈ S i := by
      have h := (S i).sub_mem ht hs
      have heq : (x + t • v - a i) - (x + s • v - a i) =
          (t - s) • v := by
        rw [sub_smul]
        abel
      rwa [heq] at h
    have hvS := (S i).smul_mem (t - s)⁻¹ hdiff
    apply hv' i
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hts), one_smul]
      using hvS
  have hbad : bad.Finite := by
    have hu : (⋃ i, {t : ℝ | x + t • v - a i ∈ S i}).Finite :=
      Set.finite_iUnion (fun i => (hsingle i).finite)
    have heq : bad = ⋃ i, {t : ℝ | x + t • v - a i ∈ S i} := by
      ext t
      simp only [bad, Set.mem_setOf_eq, Set.mem_iUnion]
    rwa [← heq] at hu
  let δ : ℝ := ε / (‖v‖ + 1)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hδMul : δ * (‖v‖ + 1) = ε := by
    dsimp only [δ]
    exact div_mul_cancel₀ ε (by positivity)
  obtain ⟨t, ht, htb⟩ := (hbad.countable.dense_compl ℝ).exists_mem_open
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℝ) δ))
    ⟨0, by simpa only [Metric.mem_ball, dist_self] using hδ⟩
  have htδ : |t| < δ := by
    simpa only [Metric.mem_ball, Real.dist_0_eq_abs] using htb
  refine ⟨x + t • v, ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖v‖ ≤ |t| * (‖v‖ + 1) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
        linarith
      _ < δ * (‖v‖ + 1) :=
        mul_lt_mul_of_pos_right htδ (by positivity)
      _ = ε := hδMul
  · intro i hi
    exact ht ⟨i, hi⟩

end ChenRanks
