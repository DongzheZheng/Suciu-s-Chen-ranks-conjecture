import ChenRanks.ArrangementMeridianBasepoint
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The original complex normal as an actual real linear map, with its
native real scalar identity proved directly from the same original
complex action. No scalar-compatibility premise is supplied. -/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

def actualSingleNormalRealMap (H : ι) : (Fin d → ℂ) →ₗ[ℝ] ℂ where
  toFun v := A.normal H v
  map_add' v w := (A.normal H).map_add v w
  map_smul' r v := by
    change A.normal H ((r : ℂ) • v) = (r : ℂ) * A.normal H v
    rw [map_smul, smul_eq_mul]

@[simp] theorem actualSingleNormalRealMap_apply (H : ι) (v : Fin d → ℂ) :
    A.actualSingleNormalRealMap H v = A.normal H v := rfl

end ChenRanks.AffineArrangement
