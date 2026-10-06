import ChenRanks.QuadraticHolonomyMetabelianQuotient

/-!
# Genuine original generators and brackets in the actual holonomy quotient

The generators and bracket are descended through the native quotient
projection. Their quadratic relation containment is proved from the
native generated ideal itself, not supplied as a bracket-kernel premise.
No group, monodromy, or Malcev comparison is claimed here.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
variable {ι : Type*} (b : Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

/-- The actual vector-linear original generators in the actual quadratic
holonomy quotient. -/
def quadraticHolonomyGenerators : V →ₗ[k] QuadraticHolonomyLie k V b K :=
  (quadraticHolonomyProjection k V b K).toLinearMap.comp
    (freeVectorGenerators k V b)

/-- The actual bracket of those original generators. -/
def quadraticHolonomyGeneratorBracket :
    (⋀[k]^2 V) →ₗ[k] QuadraticHolonomyLie k V b K :=
  (quadraticHolonomyProjection k V b K).toLinearMap.comp
    (freeGeneratorBracket k V b)

@[simp] theorem quadraticHolonomyGeneratorBracket_wedge (u v : V) :
    quadraticHolonomyGeneratorBracket k V b K (exteriorWedge u v) =
      ⁅quadraticHolonomyGenerators k V b K u,
        quadraticHolonomyGenerators k V b K v⁆ := by
  simp only [quadraticHolonomyGeneratorBracket, LinearMap.comp_apply,
    freeGeneratorBracket_exteriorWedge, LieHom.map_lie, quadraticHolonomyGenerators]
  rfl

/-- The actual generated quadratic ideal kills each actual original
quadratic relation, before any further quotient or comparison. -/
theorem quadraticHolonomyGeneratorBracket_eq_zero_of_mem
    (z : ⋀[k]^2 V) (hz : z ∈ K) :
    quadraticHolonomyGeneratorBracket k V b K z = 0 := by
  apply (quadraticHolonomyProjection_eq_zero_iff k V b K _).mpr
  apply LieSubmodule.subset_lieSpan
  exact ⟨⟨z, hz⟩, rfl⟩

theorem quadraticHolonomyRelation_le_generatorBracket_ker :
    K ≤ LinearMap.ker (quadraticHolonomyGeneratorBracket k V b K) := by
  intro z hz
  exact quadraticHolonomyGeneratorBracket_eq_zero_of_mem k V b K z hz

end ChenRanks.LieComparison
