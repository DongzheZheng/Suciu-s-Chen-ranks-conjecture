import ChenRanks.ArrangementSingularH1Spanning
import ChenRanks.ArrangementEquationCupSeparation
import ChenRanks.CupIsotropicLinearEquiv

/-!
# Geometric separation in singular cohomology

The equation-class equivalence, obtained by geometric meridian detection,
pulls each maximal isotropic subspace back to logarithmic coefficients
without changing its dimension. Geometric separation then transports
through the exterior-square functor to singular first cohomology.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem singularCupKernel_separated (Q : Submodule ℂ A.singularH1)
    (hQ : IsMaximalIsotropic (relationWedge A.quadraticSingularCup) Q)
    (hdim : 2 ≤ Module.finrank ℂ Q) :
    mixedExterior Q ⊓ A.singularCupKernel = pureExterior Q := by
  let e := A.equationWindingClassEquiv
  let P := Q.comap e.toLinearMap
  have hPmap : P.map e.toLinearMap = Q :=
    Submodule.map_comap_eq_of_surjective e.surjective Q
  have hP : IsMaximalIsotropic
      (relationWedge (A.quadraticSingularCup.comp
        (exteriorPower.map 2 e.toLinearMap))) P := by
    apply (isMaximalIsotropic_map_equiv e A.quadraticSingularCup P).mp
    rw [hPmap]
    exact hQ
  change IsMaximalIsotropic (relationWedge A.equationQuadraticCup) P at hP
  have hdimP : 2 ≤ Module.finrank ℂ P := by
    have hdimEq := finrank_submodule_map_equiv e P
    rw [hPmap] at hdimEq
    exact hdimEq ▸ hdim
  have hsep : mixedExterior P ⊓
      LinearMap.ker (A.quadraticSingularCup.comp
        (exteriorPower.map 2 e.toLinearMap)) = pureExterior P :=
    A.equationQuadraticCupKernel_separated P hP hdimP
  have ht := exterior_separation_map_equiv e A.quadraticSingularCup P hsep
  rw [hPmap] at ht
  exact ht

end ChenRanks.AffineArrangement
