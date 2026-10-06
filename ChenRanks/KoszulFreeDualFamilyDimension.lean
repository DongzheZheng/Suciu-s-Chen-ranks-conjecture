import ChenRanks.KoszulFreeFamilyDimension

/-! The same actual free-piece dimension for true duals of subspaces.
This layer proves the actual dual dimension comparison before any
maximal-isotropic family specialization. -/

set_option stderrAsMessages false

noncomputable section

open scoped BigOperators

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]

attribute [local instance 2000]
  hilbertHomogeneousGroup hilbertHomogeneousMonoid hilbertHomogeneousBaseCoefficients

/-- The actual free piece of a true dual subspace has its original
subspace dimension in the binomial formula. -/
theorem freeHomogeneousDual_finrank (P : Submodule k E)
    {τ : Type*} [Fintype τ] (b : _root_.Module.Basis τ k (_root_.Module.Dual k P))
    (r : ℕ) :
    _root_.Module.finrank k (homogeneousModule k (_root_.Module.Dual k P) b ⊥ r) =
      (r + 1) * (_root_.Module.finrank k P + r).choose (r + 2) := by
  have h := homogeneousModule_zero_finrank_dimension k (_root_.Module.Dual k P) b r
  simpa only [Subspace.dual_finrank_eq] using h


variable {α : Type*} [Fintype α] (P : α → Submodule k E)
variable {τ : α → Type*} [∀ p, Fintype (τ p)]
variable (b : (p : α) → _root_.Module.Basis (τ p) k (_root_.Module.Dual k (P p)))

/-- A true finite family of true dual subspaces has the corresponding
sum of original subspace dimensions. Every summand comes from the
previous actual free-piece theorem. -/
theorem finiteDualFreeHomogeneousFamily_finrank (r : ℕ) :
    _root_.Module.finrank k
        ((p : α) → homogeneousModule k (_root_.Module.Dual k (P p)) (b p) ⊥ r) =
      ∑ p : α, (r + 1) * (_root_.Module.finrank k (P p) + r).choose (r + 2) := by
  classical
  have h := finiteFreeHomogeneousFamily_finrank k
    (fun p => _root_.Module.Dual k (P p)) b r
  simpa only [Subspace.dual_finrank_eq] using h


end ChenRanks.Koszul
