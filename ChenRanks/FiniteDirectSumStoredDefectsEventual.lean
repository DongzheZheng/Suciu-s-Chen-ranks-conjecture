import ChenRanks.FiniteDirectSumMapEventualBijection
import Mathlib.Algebra.Module.NatInt

/-!
# Eventual bijectivity with the actual stored degree-map parents

The degree map and both actual finiteness proofs retain ordinary
additive and scalar parameters, rather than rebuilding those parameters
by typeclass search at an original endpoint. The source needs only its
stored additive monoid. The ring-module construction of its additive
group keeps that monoid unchanged and is used only in the certified
generic kernel-injectivity criterion. The target keeps its actual
group, so the actual native quotient relation is unchanged.

The finite kernel and cokernel proofs are inputs to this generic
structural tool. A mathematical endpoint must supply their previously
proved original finiteness declarations. No effective threshold is
asserted.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

theorem finiteDirectSumStoredDefects_exists_eventually_bijective
    (R : Type*) [Ring R] {M N : ℕ → Type*}
    {aM : ∀ n, AddCommMonoid (M n)}
    {aN : ∀ n, AddCommGroup (N n)}
    {sM : ∀ n, @_root_.Module R (M n) (inferInstance : Semiring R) (aM n)}
    {sN : ∀ n, @_root_.Module R (N n) (inferInstance : Semiring R)
      (aN n).toAddCommMonoid}
    (f : letI := aM; letI := aN; letI := sM; letI := sN;
      ∀ n, M n →ₗ[R] N n)
    (hK : letI := aM; letI := aN; letI := sM; letI := sN;
      _root_.Module.Finite R (⨁ n, LinearMap.ker (f n)))
    (hC : letI := aM; letI := aN; letI := sM; letI := sN;
      _root_.Module.Finite R (⨁ n, (N n ⧸ LinearMap.range (f n)))) :
    ∃ B : ℕ, ∀ n ≥ B, Function.Bijective (f n) := by
  letI := aM
  letI := aN
  letI := sM
  letI := sN
  letI : ∀ n, AddCommGroup (M n) := fun n =>
    _root_.Module.addCommMonoidToAddCommGroup R
  letI : _root_.Module.Finite R (⨁ n, LinearMap.ker (f n)) := hK
  letI : _root_.Module.Finite R (⨁ n, (N n ⧸ LinearMap.range (f n))) := hC
  exact finiteDirectSumDefects_exists_eventually_bijective R M N f

end ChenRanks
