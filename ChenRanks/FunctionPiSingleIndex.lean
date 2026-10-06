import Mathlib.Logic.Function.Basic

/-! Genuine bijectivity of a dependent product map with one true index. -/

namespace ChenRanks

/-- A genuine dependent product over a subsingleton nonempty index type
has the same bijectivity test as its actual unique coordinate. -/
theorem function_pi_bijective_of_subsingleton_index
    {P M : Type*} [Subsingleton P] (p : P) {N : P → Type*}
    (f : (q : P) → M → N q) (hf : Function.Bijective (f p)) :
    Function.Bijective (fun x q => f q x) := by
  constructor
  · intro x y hxy
    exact hf.1 (congrFun hxy p)
  · intro y
    obtain ⟨x, hx⟩ := hf.2 (y p)
    refine ⟨x, funext (fun q => ?_)⟩
    cases Subsingleton.elim q p
    exact hx

end ChenRanks
