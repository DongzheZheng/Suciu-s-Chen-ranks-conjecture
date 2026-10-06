import ChenRanks.KoszulComponentDuality

/-! The original determinant pairing is symmetric under the genuine
bidual evaluation map. This identity is proved on exterior generators
from matrix transposition; no pairing compatibility is an input.
-/
noncomputable section
namespace ChenRanks.Koszul
variable (k V : Type*) [Field k] [AddCommGroup V] [_root_.Module k V]

theorem exteriorPairingDual_bidual_evaluation (n : ℕ) :
    (exteriorPower.pairingDual k (_root_.Module.Dual k V) n).comp
        (exteriorPower.map n (_root_.Module.Dual.eval k V)) =
      (exteriorPower.pairingDual k V n).flip := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
    LinearMap.flip_apply, _root_.Module.Dual.eval_apply, Function.comp_apply]
  exact Matrix.det_transpose (Matrix.of (fun i j : Fin n => f j (v i)))

@[simp] theorem exteriorPairingDual_bidual_evaluation_apply (n : ℕ)
    (x : ⋀[k]^n V) (a : ⋀[k]^n (_root_.Module.Dual k V)) :
    exteriorPower.pairingDual k (_root_.Module.Dual k V) n
      (exteriorPower.map n (_root_.Module.Dual.eval k V) x) a =
      exteriorPower.pairingDual k V n a x :=
  DFunLike.congr_fun (DFunLike.congr_fun
    (exteriorPairingDual_bidual_evaluation k V n) x) a

end ChenRanks.Koszul
