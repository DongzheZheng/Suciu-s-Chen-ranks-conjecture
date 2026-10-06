import ChenRanks.ArrangementRationalSeparation
import ChenRanks.ResonanceSeparatedMaximalCover

/-!
# Actual arrangement separation for the genuine rational-kernel quotient

The quotient map here is literally Lambda^2 E -> Lambda^2 E / ker(Phi),
where Phi is the actual logarithmic quadratic realization of the original
arrangement. Its isotropic and maximal isotropic subspaces coincide with
those of Phi because the two actual linear maps have the same kernel.
Thus the proved arrangement separation supplies the whole hypothesis
required by the genuine algebraic Koszul/resonance theorems.

This is the rational logarithmic quotient model. Identifying its kernel
with the actual native singular cup kernel, and the Chen comparison,
remain separate theorems. No such identification is assumed here.
-/

noncomputable section

namespace ChenRanks

open Resonance

namespace AffineArrangement

attribute [local irreducible] quadraticLogarithmicRealization logarithmicRealization

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Maximal isotropy for the actual quotient is exactly maximal isotropy
for the original arrangement's actual logarithmic quadratic map. -/
theorem rationalQuadraticKernel_cupQuotient_maximal_iff
    (P : Submodule ℂ (ι → ℂ)) :
    IsMaximalIsotropic (relationWedge (cupQuotient A.rationalQuadraticKernel)) P ↔
      IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P := by
  exact isMaximalIsotropic_kernel_quotient_iff
    A.quadraticLogarithmicRealization P

/-- The actual quotient's maximal isotropic subspaces satisfy the real
arrangement separation equality without a separation premise. -/
theorem rationalQuadraticKernel_cupQuotient_separated
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge (cupQuotient A.rationalQuadraticKernel)) P)
    (hdim : 2 ≤ Module.finrank ℂ P) :
    mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P := by
  exact A.rationalQuadraticKernel_separated P
    ((A.rationalQuadraticKernel_cupQuotient_maximal_iff P).mp hP) hdim

/-- The full genuine quotient separation hypothesis is a conclusion
for every actual finite complex affine arrangement. -/
theorem rationalQuadraticKernel_all_maximal_cupQuotient_separated :
    ∀ P : Submodule ℂ (ι → ℂ),
      IsMaximalIsotropic (relationWedge (cupQuotient A.rationalQuadraticKernel)) P →
      2 ≤ Module.finrank ℂ P →
        mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P := by
  intro P hP hdim
  exact A.rationalQuadraticKernel_cupQuotient_separated P hP hdim

end AffineArrangement

end ChenRanks
