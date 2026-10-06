import Lean.Elab.Tactic.ElabTerm
import Lean.Util.ShareCommon

/-!
# Structural sharing for exact proofs

`exact_shared_native` shares repeated subexpressions before and after
term elaboration. It closes the goal through `closeMainGoalUsing` and
`MVarId.checkedAssign`; the declaration is checked by Lean's kernel.
-/

namespace ChenRanks

open Lean Meta Elab Tactic

/-- Share the existing goal expression before elaboration, elaborate
against that structurally identical goal, share the resulting proof,
and use the native checked `exact` goal-closing path. The metavariable's
original target is never replaced. -/
elab "exact_shared_native " t:term : tactic =>
  closeMainGoalUsing `exact_shared_native fun target _ => do
    let sharedTarget : Expr := Lean.ShareCommon.shareCommon target
    let proof ← elabTermEnsuringType t (some sharedTarget)
    let proof ← instantiateMVars proof
    let shared : Array Expr := Lean.ShareCommon.shareCommon #[target, proof]
    return shared[1]!

end ChenRanks
