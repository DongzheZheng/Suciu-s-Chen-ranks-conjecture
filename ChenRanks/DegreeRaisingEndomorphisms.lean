import ChenRanks.LieGradedAffineAdjointNilpotence
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Actual degree-raising subspaces of original endomorphisms

The raising subspaces are defined by the actual action of the original
endomorphisms on the actual flag submodules.  Composition genuinely adds
raising degrees.  If the actual zero-th flag is the whole original space
and the actual bounded flag is zero, the corresponding actual raising
endomorphism subspace is zero.  Neither a product-vanishing detector nor
a nilpotence conclusion is supplied as an input.
-/

namespace ChenRanks.LieComparison

variable (k T : Type*) [CommSemiring k] [AddCommMonoid T] [Module k T]

/-- The actual original endomorphisms raising every actual flag degree
by the indicated natural number. -/
def degreeRaisingEndomorphisms (F : ℕ → Submodule k T) (m : ℕ) :
    Submodule k (Module.End k T) where
  carrier := {f | ∀ n : ℕ, ∀ x : T, x ∈ F n → f x ∈ F (n + m)}
  zero_mem' := by
    intro n x hx
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg n x hx
    exact Submodule.add_mem _ (hf n x hx) (hg n x hx)
  smul_mem' := by
    intro a f hf n x hx
    exact Submodule.smul_mem _ a (hf n x hx)

@[simp] theorem mem_degreeRaisingEndomorphisms
    (F : ℕ → Submodule k T) (m : ℕ) (f : Module.End k T) :
    f ∈ degreeRaisingEndomorphisms k T F m ↔
      ∀ n : ℕ, ∀ x : T, x ∈ F n → f x ∈ F (n + m) := Iff.rfl

/-- Actual original composition adds actual raising degrees. -/
theorem mul_mem_degreeRaisingEndomorphisms
    (F : ℕ → Submodule k T) (a b : ℕ) (f g : Module.End k T)
    (hf : f ∈ degreeRaisingEndomorphisms k T F a)
    (hg : g ∈ degreeRaisingEndomorphisms k T F b) :
    f * g ∈ degreeRaisingEndomorphisms k T F (a + b) := by
  intro n x hx
  have h := hf (n + b) (g x) (hg n x hx)
  have hindex : n + b + a = n + (a + b) := by omega
  rw [hindex] at h
  exact h

/-- Actual antitone flags give actual inclusion between original
raising subspaces. -/
theorem degreeRaisingEndomorphisms_antitone
    (F : ℕ → Submodule k T) (hF : Antitone F) (m n : ℕ) (hmn : m ≤ n) :
    degreeRaisingEndomorphisms k T F n ≤ degreeRaisingEndomorphisms k T F m := by
  intro f hf j x hx
  exact hF (Nat.add_le_add_left hmn j) (hf j x hx)

/-- The true unit endomorphism raises degree zero. -/
theorem one_mem_degreeRaisingEndomorphisms (F : ℕ → Submodule k T) :
    (1 : Module.End k T) ∈ degreeRaisingEndomorphisms k T F 0 := by
  intro n x hx
  simpa only [Module.End.one_apply, Nat.add_zero] using hx

/-- An actual finite flag bound kills the actual raising subspace,
with the same original endomorphisms and their true action on all vectors. -/
theorem degreeRaisingEndomorphisms_eq_bot_of_flag_bound
    (F : ℕ → Submodule k T) (hzero : F 0 = ⊤) (b : ℕ) (hbound : F b = ⊥) :
    degreeRaisingEndomorphisms k T F b = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  apply LinearMap.ext
  intro x
  have hx : x ∈ F 0 := by rw [hzero]; trivial
  have h := hf 0 x hx
  simpa only [Nat.zero_add, hbound, Submodule.mem_bot] using h

end ChenRanks.LieComparison
