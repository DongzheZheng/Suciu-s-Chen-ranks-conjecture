import ChenRanks.KoszulObjects
import ChenRanks.ExteriorSeparation

/-!
# Genuine exterior ingredients for the third Koszul differential

The genuine third tensor term and left exterior multiplication are constructed
here.  The actual alternating differential, its descent and chain relation,
and the derivative homotopy are in the subsequent short modules.

No exactness, finite presentation, or fibre/resonance comparison is assumed.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

/-- The genuine third tensor term, with the original symmetric coefficients. -/
abbrev C3 := S k V ⊗[k] (⋀[k]^3 V)

@[simp] theorem wedgeTwo_self (v : V) : exteriorWedge (k := k) v v = 0 := by
  apply Subtype.ext
  simpa only [exteriorWedge_coe, ZeroMemClass.coe_zero] using
    ExteriorAlgebra.ι_sq_zero (R := k) v

theorem wedgeTwo_swap (u v : V) :
    exteriorWedge (k := k) u v = -exteriorWedge v u := by
  apply Subtype.ext
  have h : ExteriorAlgebra.ι k u * ExteriorAlgebra.ι k v +
      ExteriorAlgebra.ι k v * ExteriorAlgebra.ι k u = 0 :=
    ExteriorAlgebra.ι_add_mul_swap u v
  simpa only [exteriorWedge_coe, Submodule.coe_neg] using
    eq_neg_of_add_eq_zero_left h

@[simp] theorem wedgeTwo_add_left (u v w : V) :
    exteriorWedge (k := k) (u + v) w = exteriorWedge u w + exteriorWedge v w := by
  simp only [← exteriorWedgeBilin_apply, map_add, LinearMap.add_apply]

@[simp] theorem wedgeTwo_add_right (u v w : V) :
    exteriorWedge (k := k) u (v + w) = exteriorWedge u v + exteriorWedge u w := by
  simp only [← exteriorWedgeBilin_apply, map_add]

@[simp] theorem wedgeTwo_smul_left (c : k) (u v : V) :
    exteriorWedge (k := k) (c • u) v = c • exteriorWedge u v := by
  simp only [← exteriorWedgeBilin_apply, map_smul, LinearMap.smul_apply]

@[simp] theorem wedgeTwo_smul_right (c : k) (u v : V) :
    exteriorWedge (k := k) u (c • v) = c • exteriorWedge u v := by
  simp only [← exteriorWedgeBilin_apply, map_smul]

/-- Left exterior multiplication, descended from the genuine alternating
three-vector product rather than an assumed multiplication operation. -/
def exteriorInsert : V →ₗ[k] (⋀[k]^2 V) →ₗ[k] (⋀[k]^3 V) :=
  (exteriorPower.alternatingMapLinearEquiv
    (R := k) (n := 2) (M := V) (N := ⋀[k]^3 V)).toLinearMap.comp
    (exteriorPower.ιMulti k 3).curryLeft

@[simp] theorem exteriorInsert_wedge (u v w : V) :
    exteriorInsert k V u (exteriorWedge v w) =
      exteriorPower.ιMulti k 3 ![u, v, w] := by
  simp only [exteriorInsert, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    exteriorWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]

end ChenRanks.Koszul
