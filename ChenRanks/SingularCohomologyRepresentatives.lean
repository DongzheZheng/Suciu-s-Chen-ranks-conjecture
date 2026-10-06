import ChenRanks.ArrangementSingularCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Genuine cocycle representatives for actual singular cohomology

The concrete quotient is the native kernel of the actual singular
coboundary modulo the native image of the preceding boundary. Its
comparison with the existing cohomology object is the library's proved
module-homology comparison. It introduces no cohomology-model hypothesis.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

private theorem quotient_class_eq_zero_iff
    (k N H : Type) [Field k] [AddCommGroup N] [Module k N]
    [AddCommGroup H] [Module k H] (B : Submodule k N)
    (e : H ≃ₗ[k] (N ⧸ B)) (c : N) :
    e.symm (B.mkQ c) = 0 ↔ c ∈ B := by
  constructor
  · intro hc
    have hq : B.mkQ c = 0 := by
      apply e.symm.injective
      simpa only [e.symm.map_zero] using hc
    exact (Submodule.Quotient.mk_eq_zero B).mp hq
  · intro hc
    have hq : B.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero B).mpr hc
    rw [hq]
    exact e.symm.map_zero

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- Actual cocycles in the original singular cochain short complex. -/
abbrev cocycles (n : ℕ) : ModuleCat.{0} k :=
  ((complex k X).sc n).moduleCatLeftHomologyData.K

/-- Actual boundaries, as a submodule of the original cocycles. -/
abbrev boundaries (n : ℕ) : Submodule k (cocycles k X n) :=
  LinearMap.range ((complex k X).sc n).moduleCatToCycles

/-- The same actual quotient, with its native module-category structures cached. -/
abbrev cocycleQuotient (n : ℕ) : ModuleCat.{0} k :=
  ((complex k X).sc n).moduleCatLeftHomologyData.H

/-- The native proved comparison of actual cohomology with its concrete quotient. -/
def representativesEquiv (n : ℕ) :
    cohomology k X n ≃ₗ[k] cocycleQuotient k X n :=
  ((complex k X).sc n).moduleCatHomologyIso.toLinearEquiv

/-- The actual class of a genuine original cocycle. -/
def cocycleClass (n : ℕ) : cocycles k X n →ₗ[k] cohomology k X n :=
  (representativesEquiv k X n).symm.toLinearMap.comp (boundaries k X n).mkQ

/-- A genuine cocycle class vanishes exactly when it is a genuine boundary. -/
theorem cocycleClass_eq_zero_iff (n : ℕ) (c : cocycles k X n) :
    cocycleClass k X n c = 0 ↔ c ∈ boundaries k X n := by
  exact quotient_class_eq_zero_iff k (cocycles k X n) (cohomology k X n)
    (boundaries k X n) (representativesEquiv k X n) c

/-- Every actual singular cohomology class has an actual cocycle representative. -/
theorem cocycleClass_surjective (n : ℕ) : Function.Surjective (cocycleClass k X n) := by
  intro h
  let e := representativesEquiv k X n
  obtain ⟨c, hc⟩ := (boundaries k X n).mkQ_surjective (e h)
  refine ⟨c, ?_⟩
  change e.symm ((boundaries k X n).mkQ c) = h
  rw [hc, e.symm_apply_apply]

end ChenRanks.SingularCohomology
