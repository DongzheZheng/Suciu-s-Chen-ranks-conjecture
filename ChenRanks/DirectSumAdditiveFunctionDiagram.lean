import Mathlib.Algebra.DirectSum.Basic

/-! Equality of actual additive functions on a genuine direct sum is
derived on the original insertions. There are no scalar-module or
linear-map structure comparisons in this generic theorem. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks

variable {ι : Type*} [DecidableEq ι] (M : ι → Type*)
variable [∀ i, AddCommMonoid (M i)]
variable {B : Type*} [AddCommMonoid B]

/-- Genuine additivity and true insertion identities determine the
unchanged functions on the whole original direct sum. -/
theorem directSumAdditiveFunctionDiagram_of_of
    (f g : (⨁ i, M i) → B)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfadd : ∀ x y, f (x + y) = f x + f y)
    (hgadd : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ i (x : M i), f (DirectSum.of M i x) = g (DirectSum.of M i x)) :
    f = g := by
  funext z
  induction z using DirectSum.induction_on with
  | zero => exact hf0.trans hg0.symm
  | of i x => exact h i x
  | add x y hx hy => rw [hfadd, hgadd, hx, hy]

end ChenRanks
