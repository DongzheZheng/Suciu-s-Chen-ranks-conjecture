import ChenRanks.ExteriorCoordinateRowDecomposition

/-! Actual dual evaluations of actual exterior contractions anticommute. -/

noncomputable section
namespace ChenRanks.Koszul

variable (k V : Type*) [Field k] [AddCommGroup V] [_root_.Module k V]

/-- Native contractions, with no nondegeneracy, basis, or rank premise. -/
theorem functional_pointDeltaTwo_swap (a b : V →ₗ[k] k) :
    a.comp (pointDeltaTwo k V b) = -(b.comp (pointDeltaTwo k V a)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : exteriorPower.ιMulti k 2 v = exteriorWedge (v 0) (v 1) := by
    change exteriorPower.ιMulti k 2 v = exteriorPower.ιMulti k 2 ![v 0, v 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  change a (pointDeltaTwo k V b (exteriorPower.ιMulti k 2 v)) =
    -(b (pointDeltaTwo k V a (exteriorPower.ιMulti k 2 v)))
  rw [hv, pointDeltaTwo_wedge, pointDeltaTwo_wedge]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

end ChenRanks.Koszul
