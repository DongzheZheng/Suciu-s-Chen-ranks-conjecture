import ChenRanks.KoszulThirdDescent
import ChenRanks.KoszulPolynomialHomotopy

/-! The genuine consecutive Koszul differentials compose to zero. -/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

theorem delta2_delta3Linear :
    (delta2 k V).restrictScalars k ∘ₗ delta3Linear k V = 0 := by
  apply exteriorPower.linearMap_ext
  ext a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, delta3Linear_wedge, map_add, map_sub, map_smul,
    delta2_tmul, delta2Linear_exteriorWedge, smul_sub, smul_smul,
    LinearMap.zero_apply]
  simp only [one_mul, mul_comm]
  abel

/-- The genuine consecutive differentials compose to zero. -/
theorem delta2_comp_delta3 : delta2 k V ∘ₗ delta3 k V = 0 := by
  apply AlgebraTensorModule.ext
  intro s w
  simp only [LinearMap.comp_apply, delta3_tmul, map_smul]
  have hw := DFunLike.congr_fun (delta2_delta3Linear k V) w
  simpa using congrArg (fun z : C1 k V ↦ s • z) hw

end ChenRanks.Koszul
