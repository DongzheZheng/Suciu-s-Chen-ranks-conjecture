import ChenRanks.SingularCocycleCochains
import ChenRanks.SingularCupCocycleDescent

/-!
# Genuine native singular cohomology evaluated on original cycles

The cycle is an element of the original singular chain module with zero
original singular boundary. Thus actual native coboundaries evaluate to
zero, and evaluation descends through the actual native cocycle quotient.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- Literal evaluation in the original singular chain module. -/
def chainCocycleEvaluation (n : ℕ) (z : (chains k X).X (n + 1)) :
    cocycles k X (n + 1) →ₗ[k] k where
  toFun a := cocycleCochain k X (n + 1) a z
  map_add' a b := by simp only [map_add, LinearMap.add_apply]
  map_smul' c a := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Genuine coboundaries vanish on a genuine original singular cycle. -/
theorem boundaries_le_ker_chainCocycleEvaluation (n : ℕ)
    (z : (chains k X).X (n + 1)) (hz : ((chains k X).d (n + 1) n).hom z = 0) :
    boundaries k X (n + 1) ≤ LinearMap.ker (chainCocycleEvaluation k X n z) := by
  intro a ha
  obtain ⟨b, hb⟩ := (mem_positive_boundaries_iff k X n a).mp ha
  change cocycleCochain k X (n + 1) a z = 0
  rw [← hb]
  change b (((chains k X).d (n + 1) n).hom z) = 0
  rw [hz, map_zero]

/-- Evaluation of original native cohomology on a genuine original singular cycle. -/
def cycleEvaluation (n : ℕ) (z : (chains k X).X (n + 1))
    (hz : ((chains k X).d (n + 1) n).hom z = 0) :
    cohomology k X (n + 1) →ₗ[k] k :=
  ((boundaries k X (n + 1)).liftQ (chainCocycleEvaluation k X n z)
    (boundaries_le_ker_chainCocycleEvaluation k X n z hz)).comp
      (representativesEquiv k X (n + 1)).toLinearMap

/-- Native quotient descent retains exact evaluation on original cocycle representatives. -/
theorem cycleEvaluation_cocycleClass (n : ℕ) (z : (chains k X).X (n + 1))
    (hz : ((chains k X).d (n + 1) n).hom z = 0) (a : cocycles k X (n + 1)) :
    cycleEvaluation k X n z hz (cocycleClass k X (n + 1) a) =
      cocycleCochain k X (n + 1) a z := by
  change (boundaries k X (n + 1)).liftQ (chainCocycleEvaluation k X n z)
    (boundaries_le_ker_chainCocycleEvaluation k X n z hz)
      ((representativesEquiv k X (n + 1))
        ((representativesEquiv k X (n + 1)).symm ((boundaries k X (n + 1)).mkQ a))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Genuine cup evaluation on original two-cycles is its genuine cochain-product value. -/
theorem cycleEvaluation_cup_cocycleClass (z : (chains k X).X 2)
    (hz : ((chains k X).d 2 1).hom z = 0) (a b : cocycles k X 1) :
    cycleEvaluation k X 1 z hz (cup k X (cocycleClass k X 1 a) (cocycleClass k X 1 b)) =
      cupOne k X (cocycleCochain k X 1 a) (cocycleCochain k X 1 b) z := by
  rw [cup_cocycleClass, cycleEvaluation_cocycleClass, cocycleCochain_cocycleCup]

end ChenRanks.SingularCohomology
