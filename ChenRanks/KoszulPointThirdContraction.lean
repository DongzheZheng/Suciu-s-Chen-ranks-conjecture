import ChenRanks.KoszulPointContraction
import ChenRanks.KoszulThirdDescent

/-!
# Genuine third contraction at an actual point

The contraction is obtained by evaluating the actual third Koszul formula.
A normalized vector supplies an actual exterior homotopy.  This proves
pointwise exactness away from the origin without characteristic-zero or
finite-dimensional hypotheses; it is not a tensor-fibre definition.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

/-- An exterior calculation for arbitrary actual linear maps with the
standard pure exterior formulas. The formulas, rather than the sought
homotopy or exactness, are the only interface premises. -/
theorem exteriorContraction_insert_identity (a : V →ₗ[k] k)
    (f : (⋀[k]^3 V) →ₗ[k] (⋀[k]^2 V)) (g : (⋀[k]^2 V) →ₗ[k] V)
    (hf : ∀ v : Fin 3 → V, f (exteriorPower.ιMulti k 3 v) =
      a (v 0) • exteriorWedge (v 1) (v 2) -
        a (v 1) • exteriorWedge (v 0) (v 2) +
          a (v 2) • exteriorWedge (v 0) (v 1))
    (hg : ∀ u v : V, g (exteriorWedge u v) = a u • v - a v • u)
    (u : V) (w : ⋀[k]^2 V) :
    f (exteriorInsert k V u w) = a u • w - exteriorWedge u (g w) := by
  have he : f.comp (exteriorInsert k V u) =
      a u • (LinearMap.id : (⋀[k]^2 V) →ₗ[k] (⋀[k]^2 V)) -
        (exteriorWedgeBilin (k := k) u).comp g := by
    apply exteriorPower.linearMap_ext
    ext v
    have hv : exteriorPower.ιMulti k 2 v = exteriorWedge (v 0) (v 1) := by
      change exteriorPower.ιMulti k 2 v = exteriorPower.ιMulti k 2 ![v 0, v 1]
      congr 1
      ext i
      fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, hv,
      exteriorInsert_wedge, hf, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hg, map_sub, map_smul, exteriorWedgeBilin_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    abel
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, exteriorWedgeBilin_apply] using DFunLike.congr_fun he w

/-- Evaluate the actual third differential on its actual constant exterior input. -/
def pointDeltaThree (a : V →ₗ[k] k) : (⋀[k]^3 V) →ₗ[k] (⋀[k]^2 V) :=
  (specializePolynomialTensor k V (⋀[k]^2 V) a).comp (delta3Linear k V)

@[simp] theorem pointDeltaThree_wedge (a : V →ₗ[k] k) (v : Fin 3 → V) :
    pointDeltaThree k V a (exteriorPower.ιMulti k 3 v) =
      a (v 0) • exteriorWedge (v 1) (v 2) -
        a (v 1) • exteriorWedge (v 0) (v 2) +
          a (v 2) • exteriorWedge (v 0) (v 1) := by
  simp only [pointDeltaThree, LinearMap.comp_apply, delta3Linear_wedge,
    map_add, map_sub, specializePolynomialTensor_smul, specializePolynomialTensor_tmul,
    map_one, pointEvaluation_generator, one_smul]

/-- The actual polynomial third differential specializes to the actual
third contraction, with its actual evaluated polynomial coefficient. -/
theorem specialize_delta3_tmul (a : V →ₗ[k] k) (s : S k V) (w : ⋀[k]^3 V) :
    specializePolynomialTensor k V (⋀[k]^2 V) a (delta3 k V (s ⊗ₜ[k] w)) =
      pointEvaluation k V a s • pointDeltaThree k V a w := by
  rw [delta3_tmul, specializePolynomialTensor_smul]
  rfl

theorem pointDeltaTwo_comp_pointDeltaThree (a : V →ₗ[k] k) :
    (pointDeltaTwo k V a).comp (pointDeltaThree k V a) = 0 := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    pointDeltaThree_wedge, map_add, map_sub, map_smul, pointDeltaTwo_wedge,
    smul_sub, smul_smul, LinearMap.zero_apply]
  module

/-- The genuine exterior homotopy, proved on the actual exterior generators
and then extended by the universal property of the second exterior power. -/
theorem pointDeltaThree_exteriorInsert (a : V →ₗ[k] k) (u : V) (w : ⋀[k]^2 V) :
    pointDeltaThree k V a (exteriorInsert k V u w) =
      a u • w - exteriorWedge u (pointDeltaTwo k V a w) := by
  exact exteriorContraction_insert_identity k V a
    (pointDeltaThree k V a) (pointDeltaTwo k V a)
    (pointDeltaThree_wedge k V a) (pointDeltaTwo_wedge k V a) u w

/-- Pointwise third-differential exactness away from the origin, with an
actual exterior preimage obtained from a normalized vector. -/
theorem pointDeltaThree_range_eq_ker (a : V →ₗ[k] k) (ha : a ≠ 0) :
    LinearMap.range (pointDeltaThree k V a) = LinearMap.ker (pointDeltaTwo k V a) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact DFunLike.congr_fun (pointDeltaTwo_comp_pointDeltaThree k V a) w
  · intro w hw
    obtain ⟨u, hu⟩ := exists_point_normalized_vector k V a ha
    refine ⟨exteriorInsert k V u w, ?_⟩
    have hw0 : pointDeltaTwo k V a w = 0 := LinearMap.mem_ker.mp hw
    rw [pointDeltaThree_exteriorInsert, hu, hw0, one_smul]
    simp only [← exteriorWedgeBilin_apply, map_zero, sub_zero]

end ChenRanks.Koszul
