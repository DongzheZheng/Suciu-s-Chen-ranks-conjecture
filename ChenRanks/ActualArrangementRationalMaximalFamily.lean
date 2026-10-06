import ChenRanks.ActualArrangementRationalSeparationForCupQuotient
import ChenRanks.MaximalIsotropicFiniteFamily

/-!
# The actual finite rational maximal-isotropic family of an arrangement

The original arrangement supplies its actual exterior realization and the
proved geometric separation. The finite family and its dimension counts
are then constructed from those original maximal isotropic subspaces.
No finite-family, component-list, or separation assumption is an input.

These are intrinsic counts for the rational logarithmic kernel. A
comparison with native singular cohomology, irreducible components of its
topological resonance, and group Chen ranks remains to be proved.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

attribute [local irreducible] quadraticLogarithmicRealization logarithmicRealization

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The family of actual original maximal isotropic spaces of dimension
at least two is finite, with geometric separation already derived. -/
theorem rational_maximal_isotropic_finite :
    {P : Submodule ℂ (ι → ℂ) |
      IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P ∧
        2 ≤ Module.finrank ℂ P}.Finite :=
  Resonance.original_maximal_isotropic_finite_of_separated
    A.quadraticLogarithmicRealization
    (fun P hP hdim ↦ A.rationalQuadraticKernel_separated P hP hdim)

/-- The genuine original maximal-isotropic family; its elements are the
original subspaces, together with their actual maximality and dimension. -/
abbrev RationalMaximalIsotropicFamily :=
  Resonance.OriginalMaximalIsotropicFamily A.quadraticLogarithmicRealization

/-- Its finite enumeration is constructed from the proved finite set. -/
@[implicit_reducible]
def rationalMaximalIsotropicFamilyFintype :
    Fintype A.RationalMaximalIsotropicFamily :=
  A.rational_maximal_isotropic_finite.fintype

/-- The cardinality of the actual dimension-m fiber of the original family. -/
def rationalMaximalIsotropicDimensionCount (m : ℕ) : ℕ :=
  Resonance.originalMaximalIsotropicDimensionCount
    A.quadraticLogarithmicRealization
    (fun P hP hdim ↦ A.rationalQuadraticKernel_separated P hP hdim) m

/-- A positive intrinsic count means precisely that an original maximal
isotropic subspace of that dimension exists. -/
theorem rationalMaximalIsotropicDimensionCount_pos_iff (m : ℕ) :
    0 < A.rationalMaximalIsotropicDimensionCount m ↔
      ∃ P : Submodule ℂ (ι → ℂ),
        IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P ∧
        2 ≤ Module.finrank ℂ P ∧ Module.finrank ℂ P = m :=
  Resonance.originalMaximalIsotropicDimensionCount_pos_iff
    A.quadraticLogarithmicRealization
    (fun P hP hdim ↦ A.rationalQuadraticKernel_separated P hP hdim) m

/-- There are no dimension-zero or dimension-one entries. -/
theorem rationalMaximalIsotropicDimensionCount_eq_zero_of_lt_two
    (m : ℕ) (hm : m < 2) :
    A.rationalMaximalIsotropicDimensionCount m = 0 :=
  Resonance.originalMaximalIsotropicDimensionCount_eq_zero_of_lt_two
    A.quadraticLogarithmicRealization
    (fun P hP hdim ↦ A.rationalQuadraticKernel_separated P hP hdim) m hm

/-- The intrinsic count vanishes beyond the dimension of the original
coefficient space, including the empty-label and one-label boundaries. -/
theorem rationalMaximalIsotropicDimensionCount_eq_zero_of_finrank_lt
    (m : ℕ) (hm : Module.finrank ℂ (ι → ℂ) < m) :
    A.rationalMaximalIsotropicDimensionCount m = 0 :=
  Resonance.originalMaximalIsotropicDimensionCount_eq_zero_of_finrank_lt
    A.quadraticLogarithmicRealization
    (fun P hP hdim ↦ A.rationalQuadraticKernel_separated P hP hdim) m hm

end ChenRanks.AffineArrangement
