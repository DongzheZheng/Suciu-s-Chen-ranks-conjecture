import ChenRanks.CharactersSingularFirstCohomology

/-! A genuine character's original singular class evaluated on a genuine
closed continuous path. The loop is constructed from that path's actual
endpoint equality, and the cochain value is the original based-path
character evaluation. No period or cohomology evaluation is assumed.
-/
noncomputable section
namespace ChenRanks.SingularCohomology
open unitInterval
variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
variable (k : Type) [Field k]

/-- The same actual closed continuous curve, as an actual original based loop. -/
def closedContinuousPathLoop (γ : C(I, X)) (hγ : γ 0 = γ 1) : Path (γ 0) (γ 0) :=
  ⟨γ, rfl, hγ.symm⟩

theorem characterFirstClass_closedPathEvaluation (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k)
    (γ : C(I, X)) (hγ : γ 0 = γ 1) :
    closedPathEvaluation k X γ hγ (characterFirstCohomologyClass X k base χ) =
      ChenRanks.basedPathCharacterValue X k base χ
        (closedContinuousPathLoop X γ hγ) := by
  rw [characterFirstCohomologyClass, closedPathEvaluation_cocycleClass,
    cocycleCochain_toCocycle]
  exact characterOneCochain_path_value X k base χ
    (closedContinuousPathLoop X γ hγ)

end ChenRanks.SingularCohomology
