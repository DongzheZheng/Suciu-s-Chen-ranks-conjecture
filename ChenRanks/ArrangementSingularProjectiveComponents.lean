import ChenRanks.ArrangementSingularMaximalFamily
import ChenRanks.ArrangementSingularResonanceDictionary
import ChenRanks.ActualProjectiveResonanceComponentCounts

/-!
# Actual native projective components for arrangement cohomology

The basis is chosen in the actual dual of native H¹. The projective
scheme is the native Proj of the original Koszul-module annihilator
quotient. At actual vector evaluation points its support is exactly the
original singular resonance set. Native irreducible-component dimensions
are the actual vector-span dimensions, and their fiber counts are proved
equal to the original logarithmic counts.

These are component-count dictionaries. No Chen-rank comparison or
effective degree bound is asserted by this file.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace ChenRanks.AffineArrangement

open Koszul Resonance

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- A genuine finite basis of the actual dual singular first cohomology. -/
def singularDualBasis := _root_.Module.finBasis ℂ (_root_.Module.Dual ℂ A.singularH1)

/-- The genuine annihilator-quotient Proj for the actual singular cup. -/
abbrev SingularProjectiveResonanceScheme :=
  actualProjectiveResonanceScheme ℂ (_root_.Module.Dual ℂ A.singularH1) A.singularDualBasis
    (exteriorAnnihilator ℂ A.singularH1 2 A.singularCupKernel)

theorem singular_vectorProjectivePoint_mem_annihilatorZeroLocus
    {a : A.singularH1} (ha : a ≠ 0) :
    vectorProjectivePoint ℂ A.singularH1 A.singularDualBasis a ha ∈
      ProjectiveSpectrum.zeroLocus
        (homogeneousS ℂ (_root_.Module.Dual ℂ A.singularH1) A.singularDualBasis)
        (_root_.Module.annihilator (S ℂ (_root_.Module.Dual ℂ A.singularH1))
          (Koszul.Module ℂ (_root_.Module.Dual ℂ A.singularH1)
            (exteriorAnnihilator ℂ A.singularH1 2 A.singularCupKernel)) :
              Set (S ℂ (_root_.Module.Dual ℂ A.singularH1))) ↔
      a ∈ A.singularResonance :=
  vectorProjectivePoint_mem_annihilatorZeroLocus ℂ A.singularH1 A.singularDualBasis
    A.singularCupKernel ha

private theorem singularCupKernel_all_maximal_separated :
    ∀ P : Submodule ℂ A.singularH1,
      IsMaximalIsotropic (relationWedge (cupQuotient A.singularCupKernel)) P →
        2 ≤ _root_.Module.finrank ℂ P → mixedExterior P ⊓ A.singularCupKernel = pureExterior P := by
  intro P hP hdim
  exact A.singularCupKernel_separated P
    ((isMaximalIsotropic_kernel_quotient_iff A.quadraticSingularCup P).mp hP) hdim

/-- Dimensions are computed from actual native component vector spans. -/
def singularProjectiveComponentDimensionCount (m : ℕ) : ℕ :=
  actualProjectiveResonanceComponentDimensionCount ℂ A.singularH1 A.singularDualBasis
    A.singularCupKernel m

theorem singularProjectiveComponentDimensionCount_eq_singularMaximal (m : ℕ) :
    A.singularProjectiveComponentDimensionCount m =
      A.singularMaximalIsotropicDimensionCount m := by
  unfold singularProjectiveComponentDimensionCount singularMaximalIsotropicDimensionCount
  rw [actualProjectiveResonanceComponentDimensionCount_eq ℂ A.singularH1
    A.singularDualBasis A.singularCupKernel A.singularCupKernel_all_maximal_separated]
  exact originalMaximalIsotropicDimensionCount_kernel_quotient A.quadraticSingularCup
    (fun P hP hdim => A.singularCupKernel_separated P hP hdim) m

theorem singularProjectiveComponentDimensionCount_eq_rational (m : ℕ) :
    A.singularProjectiveComponentDimensionCount m =
      A.rationalMaximalIsotropicDimensionCount m :=
  (A.singularProjectiveComponentDimensionCount_eq_singularMaximal m).trans
    (A.singularMaximalIsotropicDimensionCount_eq_rational m)

end ChenRanks.AffineArrangement
