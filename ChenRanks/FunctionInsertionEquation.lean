import Mathlib.Logic.Function.Basic

/-! An opaque, scalar-independent composition rule for genuine function
insertion equalities. The three equalities are ordinary proved equations;
the conclusion is obtained by transitivity and congruence. -/

namespace ChenRanks

/-- Compose a true reconstruction equality, a true intermediate
insertion rule and a true final insertion rule without duplicating
their underlying concrete function types in local proof annotations. -/
theorem function_insertion_equation
    {A B C : Sort*} (f : A → C) (g : A → B) (h : B → C)
    (x : A) (y : B) (z : C)
    (hfg : f x = h (g x)) (hgy : g x = y) (hyz : h y = z) :
    f x = z :=
  hfg.trans ((congrArg h hgy).trans hyz)

end ChenRanks
