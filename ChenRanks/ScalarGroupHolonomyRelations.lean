import ChenRanks.ScalarGroupQuadraticRelationKernel

/-! The actual original cup-kernel annihilator is killed by the genuine
lower-central bracket. The only finiteness used is that of the original
first scalar quotient; arrangements supply this by their actual meridians.
There is no formality, comparison, degree-two vanishing or injectivity input.
-/
noncomputable section
namespace ChenRanks
variable (k G : Type) [Field k] [CharZero k] [Group G]
variable [FiniteDimensional k (scalarLowerCentralPiece k G 0)]

/-- The original group holonomy relation space, in the genuine first
lower-central quotient. Transport uses the actual canonical bidual map. -/
def scalarGroupHolonomyRelations :
    Submodule k (⋀[k]^2 (scalarLowerCentralPiece k G 0)) :=
  (Koszul.exteriorAnnihilator k (Module.Dual k (scalarLowerCentralPiece k G 0)) 2
    (scalarFirstGroupCupKernel k G)).comap
      (exteriorPower.map 2 (Module.Dual.eval k (scalarLowerCentralPiece k G 0)))

/-- Dual evaluation of a true second-degree functional proves actual
annihilator vanishing in the original second lower-central quotient. -/
theorem scalarGroupHolonomyRelations_le_bracketKernel :
    scalarGroupHolonomyRelations k G ≤ (scalarFirstExteriorBracket k G).ker := by
  intro x hx
  change scalarFirstExteriorBracket k G x = 0
  apply (Module.forall_dual_apply_eq_zero_iff k
    (scalarFirstExteriorBracket k G x)).mp
  intro ell
  have hform := scalarBracketFunctionalExterior_mem_cupKernel k G ell
  change exteriorPower.pairingDual k (Module.Dual k (scalarLowerCentralPiece k G 0)) 2
    (exteriorPower.map 2 (Module.Dual.eval k (scalarLowerCentralPiece k G 0)) x) ∈
      (scalarFirstGroupCupKernel k G).dualAnnihilator at hx
  have hz := (Submodule.mem_dualAnnihilator _).mp hx
    (scalarBracketFunctionalExterior k G ell) hform
  rw [Koszul.exteriorPairingDual_bidual_evaluation_apply,
    scalarBracketFunctionalExterior_pairing, LinearMap.comp_apply] at hz
  exact hz

namespace AffineArrangement
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- For the original arrangement and its original fundamental group,
all actual cup-dual relations vanish under the original degree-two bracket. -/
theorem actualGroupHolonomyRelations_le_bracketKernel (base : A.Complement) :
    scalarGroupHolonomyRelations k (FundamentalGroup A.Complement base) ≤
      (scalarFirstExteriorBracket k (FundamentalGroup A.Complement base)).ker :=
  scalarGroupHolonomyRelations_le_bracketKernel k (FundamentalGroup A.Complement base)

end AffineArrangement
end ChenRanks
