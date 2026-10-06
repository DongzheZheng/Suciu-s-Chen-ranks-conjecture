import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Direct-sum grading of a genuine finite product

The finite product is the ordinary dependent function type. Its grading
is constructed from actual degreewise direct sums by native DFinsupp
equivalences, genuine sigma currying, and an explicit index swap. The
equivalence and its coordinate formula are derived, not supplied.
-/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable (R : Type*) [Semiring R]
variable {P : Type*} [Fintype P] (A : P → ℕ → Type*)
variable [∀ p n, AddCommMonoid (A p n)] [∀ p n, Module R (A p n)]

/-- True swap of the component and degree indices. -/
private def componentDegreeSwap : (Σ _ : ℕ, P) ≃ (Σ _ : P, ℕ) where
  toFun x := ⟨x.2, x.1⟩
  invFun x := ⟨x.2, x.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A degreewise finite product reconstructs the true product of the
original direct sums; finiteness is used solely for the product index. -/
def directSumFiniteProductGradingEquiv :
    (⨁ n, (p : P) → A p n) ≃ₗ[R] (p : P) → ⨁ n, A p n := by
  classical
  let e₁ : (⨁ n, (p : P) → A p n) ≃ₗ[R] ⨁ n, ⨁ p, A p n :=
    DFinsupp.mapRange.linearEquiv (fun n =>
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun p => A p n)).symm)
  let e₂ : (⨁ n, ⨁ p, A p n) ≃ₗ[R] ⨁ x : (Σ _ : ℕ, P), A x.2 x.1 :=
    (DirectSum.sigmaLcurryEquiv R).symm
  let e₃ : (⨁ x : (Σ _ : ℕ, P), A x.2 x.1) ≃ₗ[R]
      ⨁ x : (Σ _ : P, ℕ), A x.1 x.2 :=
    DirectSum.lequivCongrLeft R componentDegreeSwap
  let e₄ : (⨁ x : (Σ _ : P, ℕ), A x.1 x.2) ≃ₗ[R] ⨁ p, ⨁ n, A p n :=
    DirectSum.sigmaLcurryEquiv R
  let e₅ : (⨁ p, ⨁ n, A p n) ≃ₗ[R] (p : P) → ⨁ n, A p n :=
    DFinsupp.linearEquivFunOnFintype
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

/-- The equivalence is the actual coordinate transpose. -/
theorem directSumFiniteProductGradingEquiv_apply
    (z : ⨁ n, (p : P) → A p n) (p : P) (n : ℕ) :
    directSumFiniteProductGradingEquiv R A z p n = z n p := by
  classical
  rfl

/-- Its inverse has exactly the opposite genuine coordinate formula. -/
theorem directSumFiniteProductGradingEquiv_symm_apply
    (z : (p : P) → ⨁ n, A p n) (n : ℕ) (p : P) :
    (directSumFiniteProductGradingEquiv R A).symm z n p = z p n := by
  classical
  have h := directSumFiniteProductGradingEquiv_apply R A
    ((directSumFiniteProductGradingEquiv R A).symm z) p n
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end ChenRanks
