import ChenRanks.ArrangementParallelRelations

/-!
# Actual affine quadratic equation boundaries

The generating relations are specified solely by the original affine
normals and the actual spans of the original equation polynomials. They
do not refer to the rational quadratic kernel. Parallel pairs give their
actual coordinate wedges; an actual three-equation linear relation gives
its actual triangle boundary. The previously proved genuine logarithmic
identities show that this independently defined subspace is contained
in the actual rational quadratic kernel.

The reverse inclusion and the comparison with the complement's actual
singular cup-product kernel are not asserted here.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance affineQuadraticBoundariesDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The actual affine quadratic boundary span, defined independently
from the rational-form map by the original equations and normals. -/
def affineQuadraticEquationBoundarySpan : Submodule ℂ (⋀[ℂ]^2 (ι → ℂ)) :=
  Submodule.span ℂ {z |
    (∃ H K : ι, (∃ c : ℂ, A.normal K = c • A.normal H) ∧
      z = exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1)) ∨
    (∃ H K L : ι, A.equationPolynomial L ∈
      Submodule.span ℂ {A.equationPolynomial H, A.equationPolynomial K} ∧
        z = tripleBoundary H K L)}

/-- Every independently specified actual affine equation boundary is a
genuine rational quadratic relation. Affine offsets are retained. -/
theorem affineQuadraticEquationBoundarySpan_le_rationalQuadraticKernel :
    A.affineQuadraticEquationBoundarySpan ≤ A.rationalQuadraticKernel := by
  apply Submodule.span_le.mpr
  rintro z (hparallel | htriple)
  · obtain ⟨H, K, ⟨c, hc⟩, rfl⟩ := hparallel
    exact A.parallelPair_mem_rationalQuadraticKernel H K c hc
  · obtain ⟨H, K, L, hspan, rfl⟩ := htriple
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
    exact A.tripleBoundary_mem_rationalQuadraticKernel H K L a b hab.symm

end ChenRanks.AffineArrangement
