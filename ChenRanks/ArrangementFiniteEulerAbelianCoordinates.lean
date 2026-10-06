import ChenRanks.ArrangementFiniteEulerAxisObjects
import ChenRanks.KoszulFiniteModelAbelianCoordinates

/-! Genuine original degree-one coordinates of the actual finite Euler target.

The native degree-two-tail quotient is the original dual label space
whenever degree one survives. This specializes the genuinely proved
finite-model coordinate equivalence to the actual original arrangement,
original determinant annihilator and actual original generator maps.
No degree-one comparison or generator formula is an input.

The explicit bound 1 ≤ c is necessary: at c=0 the actual finite target
is zero, even when the original dual label space is nonzero.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (c : ℕ) (hc : 1 ≤ c)

/-- The same actual native quotient and the same original label-dual
space are genuinely linearly equivalent when degree one survives. -/
def actualFiniteEulerAxisOriginalEquiv :
    A.ActualFiniteEulerAxisQuotient c ≃ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  Koszul.finiteModelAbelianOriginalEquiv ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c hc

/-- The genuine original generator class has its genuine original
coordinate projection, derived from the actual holonomy quotient map. -/
theorem actualFiniteEulerAxisOriginalEquiv_generator (H : ι) :
    A.actualFiniteEulerAxisOriginalEquiv c hc
      (A.actualFiniteEulerAxisGeneratorClass c H) = LinearMap.proj H := by
  change Koszul.finiteModelAbelianToOriginal ℂ (Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c hc
      ((nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c) 2).mkQ
        (quadraticHolonomyToFiniteModel ℂ (Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c
            (quadraticHolonomyGenerators ℂ (Module.Dual ℂ (ι → ℂ))
              A.actualLogHolonomyLabelBasis.dualBasis
              (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
                (LinearMap.proj H)))) = LinearMap.proj H
  rw [quadraticHolonomyToFiniteModel_generator]
  rfl

/-- The genuine inverse sends each original label-dual projection to
the same original actual generator class. -/
theorem actualFiniteEulerAxisOriginalEquiv_symm_projection (H : ι) :
    (A.actualFiniteEulerAxisOriginalEquiv c hc).symm (LinearMap.proj H) =
      A.actualFiniteEulerAxisGeneratorClass c H := by
  apply (A.actualFiniteEulerAxisOriginalEquiv c hc).injective
  rw [LinearEquiv.apply_symm_apply, A.actualFiniteEulerAxisOriginalEquiv_generator c hc H]

end ChenRanks.AffineArrangement
