import ChenRanks.ArrangementCoefficientModelSeparation

/-!
# Actual rational quadratic separation for every affine arrangement

The curve field is extracted from the original arrangement's actual
isotropic logarithmic image. The actual projective polynomial scheme,
coefficient curve, graph and its native finite normalization are then
constructed. Their actual field comparisons prove the model pullbacks.
The proper mixed-descent theorem and original-basis reflection give the
original quadratic separation equality.

No model, morphism, field comparison, pullback, residue detector,
horizontal kernel, or separability hypothesis is supplied. The original
subspace's maximal isotropy and dimension are the mathematical input.
Identification with the actual topological cup-product kernel remains a
separate dependency of the Chen-rank theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks.AffineArrangement

attribute [local irreducible] projectiveCoefficientRationalMap
attribute [local irreducible] quadraticLogarithmicRealization logarithmicRealization


variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual rational quadratic kernel is separated at every original
maximal isotropic subspace of dimension at least two. All curve and model
data are constructed from the same original subspace and arrangement. -/
theorem rationalQuadraticKernel_separated
    (P : Submodule ℂ (ι → ℂ))
    (hP : IsMaximalIsotropic (relationWedge A.quadraticLogarithmicRealization) P)
    (hdim : 2 ≤ Module.finrank ℂ P) :
    mixedExterior P ⊓ A.rationalQuadraticKernel = pureExterior P := by
  classical
  obtain ⟨h, a, b, hh, hfinite, hpull, _hline⟩ :=
    A.quadratic_isotropic_subspace_admits_curve_differential_line P hdim
      (fun p q ↦ hP.1 p p.property q q.property)
  apply A.rationalQuadraticKernel_separated_of_original_curve h a b hh hfinite P hP
  intro ω
  obtain ⟨p, hp⟩ := ω.property
  obtain ⟨η, hη⟩ := hpull p
  exact ⟨η, hη.trans hp⟩

end ChenRanks.AffineArrangement
