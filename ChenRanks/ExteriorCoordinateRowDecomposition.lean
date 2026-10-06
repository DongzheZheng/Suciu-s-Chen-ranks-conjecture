import ChenRanks.KoszulPointContraction
import ChenRanks.LogarithmicRelations

/-!
# Genuine coordinate-row decomposition in the original exterior square

The row map is the already constructed actual Koszul contraction evaluated
at an original coordinate functional. The complement map is the true linear
map `x ↦ x - a(x)u`. Its actual second exterior power gives the exact
mixed-plus-complement decomposition, proved on the actual exterior
generators. No antisymmetric coefficient table or decomposition is given
as a premise.

For a coordinate functional and its actual coordinate vector, the
complement has that coordinate zero, and the contraction row also has
that coordinate zero. Passing the complementary exterior term through
the original arrangement realization and constructing its actual regular
tensor lift remains a separate step. This file does not assert the
quadratic-kernel reverse inclusion.
-/

noncomputable section

namespace ChenRanks.Koszul

section GenuineExteriorDecomposition

variable (k V : Type*) [Field k] [AddCommGroup V] [_root_.Module k V]

/-- The actual linear complement map for an actual vector and functional. -/
def coordinateComplementProjection (a : V →ₗ[k] k) (u : V) : V →ₗ[k] V :=
  LinearMap.id - a.smulRight u

@[simp]
theorem coordinateComplementProjection_apply (a : V →ₗ[k] k) (u x : V) :
    coordinateComplementProjection k V a u x = x - a x • u := rfl

private theorem complement_wedge_identity (a : V →ₗ[k] k) (u x y : V) :
    exteriorWedge (k := k) (coordinateComplementProjection k V a u x)
        (coordinateComplementProjection k V a u y) =
      exteriorWedge (k := k) x y - exteriorWedge (k := k) u (a x • y - a y • x) := by
  change (exteriorWedgeBilin (k := k) (x - a x • u)) (y - a y • u) =
    (exteriorWedgeBilin (k := k) x) y -
      (exteriorWedgeBilin (k := k) u) (a x • y - a y • x)
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  change exteriorWedge (k := k) x y - a x • exteriorWedge (k := k) u y -
      a y • (exteriorWedge (k := k) x u - a x • exteriorWedge (k := k) u u) =
    exteriorWedge (k := k) x y -
      (a x • exteriorWedge (k := k) u y - a y • exteriorWedge (k := k) u x)
  simp only [wedge_self, smul_zero, sub_zero]
  rw [wedge_swap x u]
  simp only [smul_neg]
  abel

/-- The actual complementary exterior map is identity minus the true
mixed contraction term. Normalization is not needed for this identity. -/
theorem exteriorComplementProjection_eq_id_sub_contraction
    (a : V →ₗ[k] k) (u : V) :
    exteriorPower.map 2 (coordinateComplementProjection k V a u) =
      (LinearMap.id : (⋀[k]^2 V) →ₗ[k] (⋀[k]^2 V)) -
        (exteriorWedgeBilin (k := k) u).comp (pointDeltaTwo k V a) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : exteriorPower.ιMulti k 2 v = exteriorWedge (v 0) (v 1) := by
    change exteriorPower.ιMulti k 2 v = exteriorPower.ιMulti k 2 ![v 0, v 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hqv : exteriorPower.ιMulti k 2
      (fun i ↦ coordinateComplementProjection k V a u (v i)) =
      exteriorWedge (coordinateComplementProjection k V a u (v 0))
        (coordinateComplementProjection k V a u (v 1)) := by
    change exteriorPower.ιMulti k 2
      (fun i ↦ coordinateComplementProjection k V a u (v i)) =
        exteriorPower.ιMulti k 2 ![coordinateComplementProjection k V a u (v 0),
          coordinateComplementProjection k V a u (v 1)]
    congr 1
    ext i
    fin_cases i <;> rfl
  change exteriorPower.map 2 (coordinateComplementProjection k V a u)
      (exteriorPower.ιMulti k 2 v) =
    ((LinearMap.id : (⋀[k]^2 V) →ₗ[k] (⋀[k]^2 V)) -
      (exteriorWedgeBilin (k := k) u).comp (pointDeltaTwo k V a))
        (exteriorPower.ιMulti k 2 v)
  rw [exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti k 2
      (fun i ↦ coordinateComplementProjection k V a u (v i)) =
    ((LinearMap.id : (⋀[k]^2 V) →ₗ[k] (⋀[k]^2 V)) -
      (exteriorWedgeBilin (k := k) u).comp (pointDeltaTwo k V a))
        (exteriorPower.ιMulti k 2 v)
  rw [hqv]
  simp only [hv, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    pointDeltaTwo_wedge, exteriorWedgeBilin_apply]
  exact complement_wedge_identity k V a u (v 0) (v 1)

/-- Every genuine exterior vector splits into its actual contraction
row wedged with u and its actual complementary exterior term. -/
theorem exteriorCoordinateRow_decomposition (a : V →ₗ[k] k) (u : V)
    (z : ⋀[k]^2 V) :
    z = exteriorWedge u (pointDeltaTwo k V a z) +
      exteriorPower.map 2 (coordinateComplementProjection k V a u) z := by
  rw [exteriorComplementProjection_eq_id_sub_contraction]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    exteriorWedgeBilin_apply]
  abel

/-- When the vector is actually normalized, the actual complement map
lands in the actual kernel of the original functional. -/
theorem coordinateComplementProjection_mem_kernel
    (a : V →ₗ[k] k) (u : V) (hu : a u = 1) (x : V) :
    coordinateComplementProjection k V a u x ∈ LinearMap.ker a := by
  rw [LinearMap.mem_ker, coordinateComplementProjection_apply, map_sub, map_smul,
    hu, smul_eq_mul, mul_one, sub_self]

end GenuineExteriorDecomposition

section ActualCoordinateRows

variable (k : Type*) [Field k] (ι : Type*)

/-- The original coordinate row is the actual Koszul contraction at
the same coordinate evaluation, rather than a prescribed table. -/
def coordinateExteriorRow (H : ι) : (⋀[k]^2 (ι → k)) →ₗ[k] (ι → k) :=
  pointDeltaTwo k (ι → k) (LinearMap.proj H)

/-- The diagonal coordinate of an actual contraction row vanishes. -/
theorem coordinateExteriorRow_self_zero (H : ι) (z : ⋀[k]^2 (ι → k)) :
    coordinateExteriorRow k ι H z H = 0 := by
  exact LinearMap.congr_fun
    (pointEvaluation_comp_pointDeltaTwo k (ι → k) (LinearMap.proj H)) z

/-- The actual row formula on an original pure wedge. -/
@[simp]
theorem coordinateExteriorRow_wedge (H : ι) (x y : ι → k) :
    coordinateExteriorRow k ι H (exteriorWedge x y) = x H • y - y H • x :=
  pointDeltaTwo_wedge k (ι → k) (LinearMap.proj H) x y

/-- The genuine original coordinate complement has its H-coordinate
zero, with normalization supplied by the actual coordinate vector. -/
theorem coordinateComplementProjection_coordinate_zero (H : ι) (x : ι → k) :
    letI : DecidableEq ι := Classical.decEq ι
    coordinateComplementProjection k (ι → k) (LinearMap.proj H) (Pi.single H 1) x H = 0 := by
  classical
  have hu : (LinearMap.proj H : (ι → k) →ₗ[k] k) (Pi.single H 1) = 1 := by simp
  exact coordinateComplementProjection_mem_kernel k (ι → k) (LinearMap.proj H)
    (Pi.single H 1) hu x

end ActualCoordinateRows

end ChenRanks.Koszul
