import ChenRanks.FiniteDirectSumEventualVanishing
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Eventual bijectivity from finite actual degreewise defects

Both direct sums are formed from the native kernels and native quotient
cokernels of the supplied degreewise maps. Their genuine base-ring
finiteness gives eventual zero degrees, from which native kernel/range
criteria prove actual degreewise bijectivity. This is an existential
statement and supplies no effective bound.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Ring R]
variable (M N : ℕ → Type*)
variable [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (N n)]
variable [∀ n, Module R (M n)] [∀ n, Module R (N n)]
variable (f : ∀ n, M n →ₗ[R] N n)

theorem finiteDirectSumDefects_exists_eventually_bijective
    [Module.Finite R (⨁ n, LinearMap.ker (f n))]
    [Module.Finite R (⨁ n, (N n ⧸ LinearMap.range (f n)))] :
    ∃ B : ℕ, ∀ n ≥ B, Function.Bijective (f n) := by
  obtain ⟨BK, hK⟩ := finiteDirectSum_exists_eventually_subsingleton R
    (fun n => LinearMap.ker (f n))
  obtain ⟨BC, hC⟩ := finiteDirectSum_exists_eventually_subsingleton R
    (fun n => N n ⧸ LinearMap.range (f n))
  refine ⟨max BK BC, ?_⟩
  intro n hn
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.subsingleton_iff_eq_bot.mp (hK n (le_trans (le_max_left _ _) hn))
  · apply LinearMap.range_eq_top.mp
    exact Submodule.Quotient.subsingleton_iff.mp (hC n (le_trans (le_max_right _ _) hn))

end ChenRanks
