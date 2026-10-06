import ChenRanks.ArrangementSingularCupKernelEquality
import ChenRanks.ActualArrangementRationalSeparationForCupQuotient

/-!
# Geometric separation for the actual equation cup map

The genuine native singular equation cup and the original logarithmic
quadratic realization have the same original coefficient kernel. Their
maximal isotropic spaces therefore agree. The independently proved
geometric separation applies to the actual native equation cup map.
This concerns the actual original equation coefficients, before proving
that their first-cohomology class map spans all native first cohomology.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open Resonance

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem equationQuadraticCup_maximal_iff_logarithmic
    (P : Submodule ℂ (ι → ℂ)) :
    IsMaximalIsotropic (relationWedge A.equationQuadraticCup) P ↔
      IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P := by
  have hnative := isMaximalIsotropic_kernel_quotient_iff A.equationQuadraticCup P
  change IsMaximalIsotropic (relationWedge (cupQuotient A.equationQuadraticCupKernel)) P ↔
    IsMaximalIsotropic (relationWedge A.equationQuadraticCup) P at hnative
  rw [A.equationQuadraticCupKernel_eq_rationalQuadraticKernel] at hnative
  exact hnative.symm.trans (A.rationalQuadraticKernel_cupQuotient_maximal_iff P)

theorem equationQuadraticCupKernel_separated
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge A.equationQuadraticCup) P)
    (hdim : 2 ≤ Module.finrank ℂ P) :
    mixedExterior P ⊓ A.equationQuadraticCupKernel = pureExterior P := by
  rw [A.equationQuadraticCupKernel_eq_rationalQuadraticKernel]
  exact A.rationalQuadraticKernel_separated P
    ((A.equationQuadraticCup_maximal_iff_logarithmic P).mp hP) hdim

theorem equationQuadraticCupKernel_cupQuotient_separated
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge (cupQuotient A.equationQuadraticCupKernel)) P)
    (hdim : 2 ≤ Module.finrank ℂ P) :
    mixedExterior P ⊓ A.equationQuadraticCupKernel = pureExterior P := by
  rw [A.equationQuadraticCupKernel_eq_rationalQuadraticKernel] at hP ⊢
  exact A.rationalQuadraticKernel_cupQuotient_separated P hP hdim

end ChenRanks.AffineArrangement
