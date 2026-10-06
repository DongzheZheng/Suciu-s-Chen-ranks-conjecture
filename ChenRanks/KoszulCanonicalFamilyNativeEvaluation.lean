import ChenRanks.KoszulCanonicalFamilyGradingTargetEquiv

set_option stderrAsMessages false


/-! Actual function evaluation of the proved original finite-family
reconstruction. The rule is a computation of its native composition,
not an action, reconstruction, or commuting-square assumption. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks

section AbstractEvaluation

variable (R : Type*) [Semiring R]
variable {P : Type*} [Fintype P]
variable (A : P → ℕ → Type*) (B : P → Type*)
variable [∀ p n, AddCommMonoid (A p n)] [∀ p n, Module R (A p n)]
variable [∀ p, AddCommMonoid (B p)] [∀ p, Module R (B p)]
variable (e : ∀ p, (⨁ n, A p n) ≃ₗ[R] B p)

/-- The genuine reconstruction evaluates by its genuine native
transpose and component equivalence. This is a computation on abstract
native scalar data, proved before concrete quotient specialization. -/
theorem finiteFamilyGradingRecomposition_toEquiv_apply
    (x : ⨁ n, (p : P) → A p n) (p : P) :
    (finiteFamilyGradingRecomposition R A B e).toEquiv x p =
      (e p).toEquiv ((directSumFiniteProductGradingEquiv R A).toEquiv x p) := rfl

end AbstractEvaluation

/- Inspect only the expression's outer constructor. No type, local
declaration, or dictionary is printed or recursively traversed. -/
private def gradingExpressionKind : Lean.Expr → String
  | .bvar _ => "bvar"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forall"
  | .letE _ _ _ _ _ => "let"
  | .lit _ => "lit"
  | .mdata _ _ => "mdata"
  | .proj _ _ _ => "proj"

/- An equality has exactly three application nodes. Bounded metadata
stripping handles annotations without inspecting the equality's type. -/
private def gradingEqualitySides : ℕ → Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | 0, _ => none
  | fuel + 1, .mdata _ body => gradingEqualitySides fuel body
  | fuel + 1, .letE _ _ value body _ =>
      gradingEqualitySides fuel (body.instantiate1 value)
  | _ + 1, .app (.app (.app (.const name _) _) lhs) rhs =>
      if name == ``Eq then some (lhs, rhs) else none
  | _ + 1, _ => none

/- A text-only diagnostic deliberately omits the large local goal from
the error-message context. This affects error reporting, not proof
construction or checking. -/
private def gradingDiagnosticFailure {α : Type} (message : String) :
    Lean.Elab.Tactic.TacticM α := do
  throw <| Lean.Exception.error (← Lean.getRef) m!"{message}"

/- A node-bounded search of application data, not typeclass types.
For applications it visits the final argument before the function.
Consequently native coercions expose their actual reconstruction value
before their large implicit dictionary arguments. -/
private def findActualGradingFactory : ℕ → List Lean.Expr → Option Lean.Expr
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, expr :: rest =>
      if expr.isAppOfArity ``ChenRanks.finiteFamilyGradingRecomposition 11 then
        some expr
      else
        match expr with
        | .app fn arg => findActualGradingFactory fuel (arg :: fn :: rest)
        | .mdata _ body => findActualGradingFactory fuel (body :: rest)
        | .proj _ _ body => findActualGradingFactory fuel (body :: rest)
        | .letE _ _ value body _ =>
            findActualGradingFactory fuel (body :: value :: rest)
        | _ => findActualGradingFactory fuel rest

/- The elaborator is defined before any concrete field, quotient, or
family variables are in scope. It reads the original factory's actual
arguments and constructs the already proved generic computation theorem
with precisely those arguments. The ordinary checked assignment and
kernel still verify the resulting proof. -/
elab "actual_native_dictionary_evaluation" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  let some (lhs, _) := gradingEqualitySides 16 target |
    gradingDiagnosticFailure "Actual reconstruction equality has no Eq head after 16 metadata/let nodes"
  let some factory := findActualGradingFactory 256 [lhs] |
    gradingDiagnosticFailure "Actual finite-family reconstruction factory not found in 256 application nodes"
  let storedArgs := factory.getAppArgs
  let lctx ← Lean.getLCtx
  let some xDecl := lctx.findFromUserName? `x |
    gradingDiagnosticFailure "Actual source element not found"
  let some pDecl := lctx.findFromUserName? `P |
    gradingDiagnosticFailure "Actual component index not found"
  let factoryName := factory.getAppFn.constName!
  let factoryLevels := factory.getAppFn.constLevels!
  let factoryInfo ← Lean.getConstInfo factoryName
  let ruleInfo ← Lean.getConstInfo ``ChenRanks.finiteFamilyGradingRecomposition_toEquiv_apply
  let levelPairs := factoryInfo.levelParams.zip factoryLevels
  let mut ruleLevels : List Lean.Level := []
  for n in ruleInfo.levelParams do
    let some pair := levelPairs.find? (fun q => q.1 == n) |
      gradingDiagnosticFailure s!"Stored universe parameter {n} was not found"
    ruleLevels := ruleLevels ++ [pair.2]
  let proof := Lean.mkAppN
    (Lean.mkConst ``ChenRanks.finiteFamilyGradingRecomposition_toEquiv_apply ruleLevels)
    (storedArgs ++ #[Lean.mkFVar xDecl.fvarId, Lean.mkFVar pDecl.fvarId])
  Lean.Elab.Tactic.closeMainGoal `actualNativeDictionaryComputation proof


end ChenRanks
