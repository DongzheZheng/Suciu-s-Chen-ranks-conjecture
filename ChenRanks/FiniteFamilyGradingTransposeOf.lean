import ChenRanks.KoszulCanonicalGradingOfFormula

/-! A genuine underlying insertion formula for the native finite-product
transpose. This is proved by the already verified reconstruction formula
with identity component equivalences; no transpose or reconstruction
property is supplied as a premise. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Semiring R]
variable {P : Type*} [Fintype P]
variable (A : P → ℕ → Type*)
variable [∀ p n, AddCommMonoid (A p n)] [∀ p n, Module R (A p n)]

/-- The actual native finite transpose carries a true degree insertion
to that same component insertion. -/
theorem directSumFiniteProductGradingEquiv_toEquiv_of
    (r : ℕ) (z : (p : P) → A p r) (p : P) :
    (directSumFiniteProductGradingEquiv R A).toEquiv
      (DirectSum.of (fun n => (p : P) → A p n) r z) p =
      DirectSum.of (A p) r (z p) :=
  finiteFamilyGradingRecomposition_toEquiv_of R A
    (fun p => ⨁ n, A p n) (fun p => LinearEquiv.refl R (⨁ n, A p n)) r z p

end ChenRanks
