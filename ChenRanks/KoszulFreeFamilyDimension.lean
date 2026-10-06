import ChenRanks.KoszulFree
import ChenRanks.KoszulCanonicalFamilyGradingObjects
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Genuine dimensions of finite products of the original free pieces.
The spaces, bases, zero relations and finite index type are actual data.
No dimension formula or decomposition is assumed. -/

set_option stderrAsMessages false

noncomputable section

open scoped BigOperators

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

local instance (priority := 2000) hilbertHomogeneousGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommGroup (homogeneousModule k V c K r) :=
  canonicalHomogeneousQuotientAddCommGroup k V c K r

local instance (priority := 2000) hilbertHomogeneousMonoid
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    AddCommMonoid (homogeneousModule k V c K r) :=
  (canonicalHomogeneousQuotientAddCommGroup k V c K r).toAddCommMonoid

local instance (priority := 2000) hilbertHomogeneousBaseCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    {τ : Type*} [Fintype τ] (c : _root_.Module.Basis τ k V)
    (K : Submodule k (⋀[k]^2 V)) (r : ℕ) :
    _root_.Module k (homogeneousModule k V c K r) :=
  canonicalHomogeneousQuotientBaseCoefficients k V c K r

variable {α : Type*} [Fintype α]
variable (V : α → Type*) [∀ p, AddCommGroup (V p)] [∀ p, _root_.Module k (V p)]
variable {τ : α → Type*} [∀ p, Fintype (τ p)]
variable (b : (p : α) → _root_.Module.Basis (τ p) k (V p))

/-- A genuine finite product of original zero-relation pieces has the
sum of their independently proved actual dimensions. -/
theorem finiteFreeHomogeneousFamily_finrank (r : ℕ) :
    _root_.Module.finrank k
        ((p : α) → homogeneousModule k (V p) (b p) ⊥ r) =
      ∑ p : α, (r + 1) * (_root_.Module.finrank k (V p) + r).choose (r + 2) := by
  classical
  rw [_root_.Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro p _hp
  exact homogeneousModule_zero_finrank_dimension k (V p) (b p) r


end ChenRanks.Koszul
