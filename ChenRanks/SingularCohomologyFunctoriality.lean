import ChenRanks.ArrangementSingularCohomology

/-!
# True pullback on singular cohomology

The pullback is the dual of the native singular-chain map induced by the
actual continuous map. Its differential identity uses the native chain-map
identity. No cohomological comparison or cup-product input is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The genuine map of native singular chains induced by a continuous map. -/
def chainMap (f : C(X, Y)) : chains k X ⟶ chains k Y :=
  ((singularChainComplexFunctor (ModuleCat.{0} k)).obj
    (ModuleCat.of k k)).map (TopCat.ofHom f)

/-- Pullback on actual singular cochains. -/
def cochainPullback (f : C(X, Y)) (n : ℕ) :
    cochains k Y n →ₗ[k] cochains k X n :=
  ((chainMap k f).f n).hom.dualMap

/-- The actual singular-chain-map identity gives the true coboundary identity. -/
theorem differential_cochainPullback (f : C(X, Y)) (n : ℕ) :
    (differential k X n).comp (cochainPullback k f n) =
      (cochainPullback k f (n + 1)).comp (differential k Y n) := by
  ext ℓ z
  have h := (chainMap k f).comm (n + 1) n
  have hz := congrArg (fun g => g.hom z) h
  change ((chains k Y).d (n + 1) n).hom (((chainMap k f).f (n + 1)).hom z) =
    ((chainMap k f).f n).hom (((chains k X).d (n + 1) n).hom z) at hz
  change ℓ (((chainMap k f).f n).hom (((chains k X).d (n + 1) n).hom z)) =
    ℓ (((chains k Y).d (n + 1) n).hom (((chainMap k f).f (n + 1)).hom z))
  exact congrArg ℓ hz.symm

/-- The actual cochain-complex pullback, with its chain identity proved above. -/
def complexPullback (f : C(X, Y)) : complex k Y ⟶ complex k X :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun n => ModuleCat.ofHom (cochainPullback k f n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact differential_cochainPullback k f n)

/-- The native induced map on actual singular cohomology. -/
def cohomologyPullback (f : C(X, Y)) (n : ℕ) :
    cohomology k Y n →ₗ[k] cohomology k X n :=
  (HomologicalComplex.homologyMap (complexPullback k f) n).hom

end ChenRanks.SingularCohomology
