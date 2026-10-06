import ChenRanks.SingularSimplexFunctoriality
import ChenRanks.SingularCupAlternation

/-!
# Actual pullback on cocycles and on cup products

Native cycle and homology naturality identify the concrete quotient
representatives with the original cohomology pullback. Thus naturality
of the true cochain product descends to the original singular cup; no
cohomology-model comparison is an input.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The native map on actual cocycles, with its concrete-kernel coordinates. -/
def cocyclePullback (f : C(X, Y)) (n : ℕ) :
    cocycles k Y n →ₗ[k] cocycles k X n :=
  (((complex k Y).sc n).moduleCatCyclesIso.inv ≫
    HomologicalComplex.cyclesMap (complexPullback k f) n ≫
    ((complex k X).sc n).moduleCatCyclesIso.hom).hom

/-- The actual underlying cochain of the native cocycle pullback. -/
theorem cocycleCochain_cocyclePullback (f : C(X, Y)) (n : ℕ)
    (a : cocycles k Y n) :
    cocycleCochain k X n (cocyclePullback k f n a) =
      cochainPullback k f n (cocycleCochain k Y n a) := by
  have hcat :
      (((complex k Y).sc n).moduleCatCyclesIso.inv ≫
        HomologicalComplex.cyclesMap (complexPullback k f) n ≫
        ((complex k X).sc n).moduleCatCyclesIso.hom) ≫
        ((complex k X).sc n).moduleCatLeftHomologyData.i =
      ((complex k Y).sc n).moduleCatLeftHomologyData.i ≫
        (complexPullback k f).f n := by
    simp only [Category.assoc]
    erw [((complex k X).sc n).moduleCatCyclesIso_hom_i]
    change ((complex k Y).sc n).moduleCatCyclesIso.inv ≫
      HomologicalComplex.cyclesMap (complexPullback k f) n ≫
      (complex k X).iCycles n = _
    erw [HomologicalComplex.cyclesMap_i (complexPullback k f) n]
    erw [← Category.assoc, ((complex k Y).sc n).moduleCatCyclesIso_inv_iCycles]
    rfl
  exact congrArg (fun g => g.hom a) hcat

/-- The original concrete class map equals the native cycle-to-homology map. -/
theorem cocycleClass_eq_native (Z : Type) [TopologicalSpace Z] (n : ℕ)
    (a : cocycles k Z n) :
    cocycleClass k Z n a =
      (((complex k Z).sc n).moduleCatCyclesIso.inv ≫
        (complex k Z).homologyπ n).hom a := by
  have h := ((complex k Z).sc n).moduleCatCyclesIso_inv_π
  exact (congrArg (fun g => g.hom a) h).symm

/-- The native pullback of an original class is the class of the original pullback. -/
theorem cohomologyPullback_cocycleClass (f : C(X, Y)) (n : ℕ)
    (a : cocycles k Y n) :
    cohomologyPullback k f n (cocycleClass k Y n a) =
      cocycleClass k X n (cocyclePullback k f n a) := by
  rw [cocycleClass_eq_native, cocycleClass_eq_native]
  have hcat :
      (((complex k Y).sc n).moduleCatCyclesIso.inv ≫
        (complex k Y).homologyπ n) ≫
        HomologicalComplex.homologyMap (complexPullback k f) n =
      (((complex k Y).sc n).moduleCatCyclesIso.inv ≫
        HomologicalComplex.cyclesMap (complexPullback k f) n ≫
        ((complex k X).sc n).moduleCatCyclesIso.hom) ≫
      (((complex k X).sc n).moduleCatCyclesIso.inv ≫
        (complex k X).homologyπ n) := by
    simp only [Category.assoc]
    erw [HomologicalComplex.homologyπ_naturality (complexPullback k f) n,
      ((complex k X).sc n).moduleCatCyclesIso.hom_inv_id_assoc]
    rfl
  exact congrArg (fun g => g.hom a) hcat

/-- The true cup of actual cocycles commutes with native pullback. -/
theorem cocyclePullback_cocycleCup (f : C(X, Y)) (a b : cocycles k Y 1) :
    cocyclePullback k f 2 (cocycleCup k Y a b) =
      cocycleCup k X (cocyclePullback k f 1 a) (cocyclePullback k f 1 b) := by
  have hinj : Function.Injective (cocycleCochain k X 2) := by
    intro x y h
    apply Subtype.ext
    exact h
  apply hinj
  rw [cocycleCochain_cocyclePullback, cocycleCochain_cocycleCup,
    cochainPullback_cupOne, cocycleCochain_cocycleCup,
    cocycleCochain_cocyclePullback, cocycleCochain_cocyclePullback]

/-- Naturality of the original singular degree-one cup product. -/
theorem cohomologyPullback_cup (f : C(X, Y)) (a b : cohomology k Y 1) :
    cohomologyPullback k f 2 (cup k Y a b) =
      cup k X (cohomologyPullback k f 1 a) (cohomologyPullback k f 1 b) := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective k Y 1 a
  obtain ⟨b, rfl⟩ := cocycleClass_surjective k Y 1 b
  rw [cup_cocycleClass, cohomologyPullback_cocycleClass,
    cohomologyPullback_cocycleClass, cohomologyPullback_cocycleClass,
    cup_cocycleClass, cocyclePullback_cocycleCup]

end ChenRanks.SingularCohomology
