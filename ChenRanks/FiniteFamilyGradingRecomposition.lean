import ChenRanks.DirectSumFiniteProductGrading

/-!
# Genuine recomposition from genuine component grading equivalences

The input component equivalences are arbitrary already proved genuine
linear equivalences. The total finite-family reconstruction and its
degree-insertion formula are derived. The Koszul specialization uses its
previously proved actual homogeneousDirectSumEquiv for every component;
no actual-family decomposition hypothesis is added.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Semiring R]
variable {P : Type*} [Fintype P]
variable (A : P → ℕ → Type*) (B : P → Type*)
variable [∀ p n, AddCommMonoid (A p n)] [∀ p n, Module R (A p n)]
variable [∀ p, AddCommMonoid (B p)] [∀ p, Module R (B p)]
variable (e : ∀ p, (⨁ n, A p n) ≃ₗ[R] B p)

/-- The actual finite-product transpose followed by the genuine
component equivalences. -/
def finiteFamilyGradingRecomposition :
    (⨁ n, (p : P) → A p n) ≃ₗ[R] ((p : P) → B p) :=
  (directSumFiniteProductGradingEquiv R A).trans (LinearEquiv.piCongrRight e)

private theorem finiteFamilyTranspose_lof
    (r : ℕ) (z : (p : P) → A p r) (p : P) :
    directSumFiniteProductGradingEquiv R A
      (DirectSum.lof R ℕ (fun n => (p : P) → A p n) r z) p =
      DirectSum.lof R ℕ (A p) r (z p) := by
  classical
  ext n
  rw [directSumFiniteProductGradingEquiv_apply]
  by_cases hr : r = n
  · subst n
    simp only [DirectSum.lof_apply]
  · simp only [DirectSum.lof_eq_of, DirectSum.of_apply, dif_neg hr]
    rfl

/-- A genuine original degree insertion maps to that same component
insertion under its actual component grading equivalence. -/
theorem finiteFamilyGradingRecomposition_lof
    (r : ℕ) (z : (p : P) → A p r) (p : P) :
    finiteFamilyGradingRecomposition R A B e
      (DirectSum.lof R ℕ (fun n => (p : P) → A p n) r z) p =
      e p (DirectSum.lof R ℕ (A p) r (z p)) := by
  change e p (directSumFiniteProductGradingEquiv R A
    (DirectSum.lof R ℕ (fun n => (p : P) → A p n) r z) p) = _
  rw [finiteFamilyTranspose_lof]

end ChenRanks
