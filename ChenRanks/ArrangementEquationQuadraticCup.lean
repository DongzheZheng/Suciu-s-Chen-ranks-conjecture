import ChenRanks.ArrangementSingularWindingClasses
import ChenRanks.SingularCupAlternation

/-!
# The original singular quadratic cup on original equation coefficients

This is the genuine exterior-square map of the original equation-class
map followed by the native singular cup. It exists before H¹ spanning
or the logarithmic/OS comparison has been proved. Its definition does
not identify these kernels or replace the original cohomology space.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open SingularCohomology

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original equation coefficient map followed by the original native singular cup. -/
def equationQuadraticCup : (⋀[ℂ]^2 (ι → ℂ)) →ₗ[ℂ] A.singularH2 :=
  A.quadraticSingularCup.comp (exteriorPower.map 2 A.equationWindingClassMap)

/-- The original genuine equation-coefficient cup kernel, before any comparison. -/
def equationQuadraticCupKernel : Submodule ℂ (⋀[ℂ]^2 (ι → ℂ)) :=
  LinearMap.ker A.equationQuadraticCup

theorem equationQuadraticCup_exteriorWedge (a b : ι → ℂ) :
    A.equationQuadraticCup (exteriorWedge (k := ℂ) a b) =
      A.singularCup (A.equationWindingClassMap a) (A.equationWindingClassMap b) := by
  change quadraticCup ℂ A.Complement
    (exteriorPower.map 2 A.equationWindingClassMap (exteriorPower.ιMulti ℂ 2 ![a, b])) = _
  rw [exteriorPower.map_apply_ιMulti]
  have hv : (fun i => A.equationWindingClassMap (![a, b] i)) =
      ![A.equationWindingClassMap a, A.equationWindingClassMap b] := by
    ext i
    fin_cases i <;> rfl
  simp only [Function.comp_def]
  rw [hv]
  exact quadraticCup_exteriorWedge ℂ A.Complement _ _

end ChenRanks.AffineArrangement
