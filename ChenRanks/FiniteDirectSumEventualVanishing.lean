import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Actual eventual vanishing of a finite graded direct sum

A genuine finite module structure on the actual direct sum supplies
finitely many actual generators. Their genuine dependent finite supports
have a common bound. Above that bound the native component map kills
every generator and hence the whole actual direct sum. Its own native
degree insertion then proves that the corresponding actual degree is
zero. No degree bound or support bound is supplied as an input.

This generic structural lemma must be applied to a proved actual
kernel/cokernel direct-sum decomposition; it does not assert such a
decomposition or a manuscript effective threshold.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Semiring R]
variable (G : ℕ → Type*) [∀ n, AddCommGroup (G n)] [∀ n, Module R (G n)]

/-- Actual finite generation of the actual direct sum itself forces
vanishing of every actual degree above a bound derived from generators. -/
theorem finiteDirectSum_exists_eventually_subsingleton
    [Module.Finite R (⨁ n : ℕ, G n)] :
    ∃ N : ℕ, ∀ n ≥ N, Subsingleton (G n) := by
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R (⨁ n : ℕ, G n)›
  let B := s.sup (fun z => z.support.sup id)
  refine ⟨B + 1, ?_⟩
  intro n hn
  have hgens : (s : Set (⨁ n : ℕ, G n)) ⊆
      LinearMap.ker (DirectSum.component R ℕ G n) := by
    intro z hz
    change z n = 0
    apply DFinsupp.notMem_support_iff.mp
    intro hmem
    have hnb : n ≤ z.support.sup id := Finset.le_sup (f := id) hmem
    have hzb : z.support.sup id ≤ B :=
      Finset.le_sup (f := fun x : ⨁ n : ℕ, G n => x.support.sup id) hz
    omega
  have htop : (⊤ : Submodule R (⨁ n : ℕ, G n)) ≤
      LinearMap.ker (DirectSum.component R ℕ G n) := by
    rw [← hs]
    exact Submodule.span_le.mpr hgens
  have hzero : ∀ v : G n, v = 0 := by
    intro v
    have hv := htop (show DirectSum.lof R ℕ G n v ∈
      (⊤ : Submodule R (⨁ n : ℕ, G n)) from trivial)
    change DirectSum.component R ℕ G n (DirectSum.lof R ℕ G n v) = 0 at hv
    simpa only [DirectSum.component.lof_self] using hv
  exact ⟨fun v w => (hzero v).trans (hzero w).symm⟩

end ChenRanks
