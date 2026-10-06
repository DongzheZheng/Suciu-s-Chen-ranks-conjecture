import ChenRanks.KoszulNativeHomogeneousEquiv
import ChenRanks.FiniteFamilyGradingRecomposition

/-!
# Underlying-function formulas for genuine original degree insertions

Both formulas below are the previously proved original formulas, with
the same underlying `DirectSum.of` insertion and the same actual
equivalence function. This isolates plain insertion evaluation from
repeated scalar-parent comparison at actual dual-subspace quotients.
No scalar compatibility, reconstruction, or diagram is a premise.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

section FiniteFamily

variable (R : Type*) [Semiring R]
variable {P : Type*} [Fintype P]
variable (A : P → ℕ → Type*) (B : P → Type*)
variable [∀ p n, AddCommMonoid (A p n)] [∀ p n, Module R (A p n)]
variable [∀ p, AddCommMonoid (B p)] [∀ p, Module R (B p)]
variable (e : ∀ p, (⨁ n, A p n) ≃ₗ[R] B p)

/-- The genuine finite-family equivalence has the same insertion
formula as an underlying function, without new linear data. -/
theorem finiteFamilyGradingRecomposition_toEquiv_of
    (r : ℕ) (z : (p : P) → A p r) (p : P) :
    (finiteFamilyGradingRecomposition R A B e).toEquiv
      (DirectSum.of (fun n => (p : P) → A p n) r z) p =
      (e p).toEquiv (DirectSum.of (A p) r (z p)) :=
  finiteFamilyGradingRecomposition_lof R A B e r z p

end FiniteFamily

namespace Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {τ : Type*} [Fintype τ] (b : _root_.Module.Basis τ k V)
variable (K : Submodule k (⋀[k]^2 V))

attribute [local instance 2500]
  nativeGradingOriginalGroup nativeGradingOriginalMonoid nativeGradingOriginalBaseCoefficients
  nativeGradingDegreeGroup nativeGradingDegreeMonoid nativeGradingDegreeBaseCoefficients

/-- The same native original grading function has precisely the original
degree inclusion on its underlying direct-sum insertion. -/
theorem nativeHomogeneousDirectSumEquiv_toEquiv_of (r : ℕ)
    (z : homogeneousModule k V b K r) :
    (nativeHomogeneousDirectSumEquiv k V b K).toEquiv
      (DirectSum.of (homogeneousModule k V b K) r z) =
      degreeQuotientInclusion k V b K r z :=
  nativeHomogeneousDirectSumEquiv_lof k V b K r z

end Koszul

end ChenRanks
