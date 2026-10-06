import ChenRanks.ExteriorCoordinateRowDecomposition

/-!
# Genuine coordinate rows and reconstruction of the actual exterior square

The rows are the actual Koszul contractions at the original coordinate
functionals. Their entries are proved antisymmetric from the true
contraction formula on exterior generators. The actual sum of coordinate
vectors wedged with these rows is twice the original exterior vector.
In characteristic zero this gives a true reconstruction map and makes
the actual coordinate rows jointly injective.

No antisymmetric table, coordinate reconstruction, or exterior-basis
identification is an assumption. These are linear-algebra interfaces
for the actual affine pair-block projections.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks.Koszul

variable (k ι : Type*) [Field k] [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

private theorem coordinate_sum_basis (x : ι → k) :
    (∑ H, x H • (Pi.single H 1 : ι → k)) = x := by
  ext H
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single H]
  · simp
  · intro K _ hKH
    simp [Pi.single_apply, hKH, Ne.symm hKH]
  · intro hH
    exact (hH (Finset.mem_univ H)).elim

omit [Fintype ι] in
private theorem exterior_generator_pair (v : Fin 2 → ι → k) :
    exteriorPower.ιMulti k 2 v = exteriorWedge (k := k) (v 0) (v 1) := by
  change exteriorPower.ιMulti k 2 v = exteriorPower.ιMulti k 2 ![v 0, v 1]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The two actual coordinate contractions have antisymmetric entries. -/
theorem coordinateExteriorRow_swap (H K : ι) (z : ⋀[k]^2 (ι → k)) :
    coordinateExteriorRow k ι H z K = -coordinateExteriorRow k ι K z H := by
  have heq : (LinearMap.proj K).comp (coordinateExteriorRow k ι H) =
      -(LinearMap.proj H).comp (coordinateExteriorRow k ι K) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change coordinateExteriorRow k ι H (exteriorPower.ιMulti k 2 v) K =
      -coordinateExteriorRow k ι K (exteriorPower.ιMulti k 2 v) H
    rw [exterior_generator_pair]
    simp only [coordinateExteriorRow_wedge, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact LinearMap.congr_fun heq z

/-- The actual sum of coordinate vectors wedged with the actual rows. -/
def coordinateExteriorRowSum : (⋀[k]^2 (ι → k)) →ₗ[k] (⋀[k]^2 (ι → k)) :=
  ∑ H, (exteriorWedgeBilin (k := k) (Pi.single H 1)).comp (coordinateExteriorRow k ι H)

@[simp]
theorem coordinateExteriorRowSum_apply (z : ⋀[k]^2 (ι → k)) :
    coordinateExteriorRowSum k ι z =
      ∑ H, exteriorWedge (k := k) (Pi.single H 1) (coordinateExteriorRow k ι H z) := by
  simp only [coordinateExteriorRowSum, LinearMap.sum_apply, LinearMap.comp_apply,
    exteriorWedgeBilin_apply]

private theorem coordinateExteriorRowSum_wedge (x y : ι → k) :
    coordinateExteriorRowSum k ι (exteriorWedge (k := k) x y) =
      (2 : k) • exteriorWedge (k := k) x y := by
  rw [coordinateExteriorRowSum_apply]
  simp only [coordinateExteriorRow_wedge]
  change (∑ H, exteriorWedgeBilin (k := k) (Pi.single H 1) (x H • y - y H • x)) = _
  simp only [map_sub, map_smul, Finset.sum_sub_distrib]
  have hx : (∑ H, x H • exteriorWedge (k := k) (Pi.single H 1) y) =
      exteriorWedge (k := k) x y := by
    calc
      (∑ H, x H • exteriorWedge (k := k) (Pi.single H 1) y) =
          exteriorWedgeBilin (k := k) (∑ H, x H • (Pi.single H 1 : ι → k)) y := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
          exteriorWedgeBilin_apply]
      _ = exteriorWedge (k := k) x y := by rw [coordinate_sum_basis]; rfl
  have hy : (∑ H, y H • exteriorWedge (k := k) (Pi.single H 1) x) =
      exteriorWedge (k := k) y x := by
    calc
      (∑ H, y H • exteriorWedge (k := k) (Pi.single H 1) x) =
          exteriorWedgeBilin (k := k) (∑ H, y H • (Pi.single H 1 : ι → k)) x := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
          exteriorWedgeBilin_apply]
      _ = exteriorWedge (k := k) y x := by rw [coordinate_sum_basis]; rfl
  simp only [exteriorWedgeBilin_apply]
  rw [hx, hy, wedge_swap y x, sub_neg_eq_add, two_smul]

/-- The true coordinate row sum is exactly twice the actual identity map. -/
theorem coordinateExteriorRowSum_eq_two_smul_id :
    coordinateExteriorRowSum k ι =
      (2 : k) • (LinearMap.id : (⋀[k]^2 (ι → k)) →ₗ[k] (⋀[k]^2 (ι → k))) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change coordinateExteriorRowSum k ι (exteriorPower.ιMulti k 2 v) =
    (2 : k) • exteriorPower.ιMulti k 2 v
  rw [exterior_generator_pair]
  exact coordinateExteriorRowSum_wedge k ι (v 0) (v 1)

variable [CharZero k]

/-- An actual exterior vector is reconstructed from its actual coordinate
rows by the genuine half-sum formula. -/
theorem exterior_eq_half_coordinateRowSum (z : ⋀[k]^2 (ι → k)) :
    z = (2 : k)⁻¹ • (∑ H, exteriorWedge (k := k) (Pi.single H 1)
      (coordinateExteriorRow k ι H z)) := by
  rw [← coordinateExteriorRowSum_apply, coordinateExteriorRowSum_eq_two_smul_id]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
    inv_mul_cancel₀ (show (2 : k) ≠ 0 by norm_num), one_smul]

/-- The genuine actual contraction rows are jointly injective. -/
theorem exterior_eq_zero_of_coordinateRows_zero (z : ⋀[k]^2 (ι → k))
    (hz : ∀ H, coordinateExteriorRow k ι H z = 0) : z = 0 := by
  rw [exterior_eq_half_coordinateRowSum k ι z]
  have hw (H : ι) : exteriorWedge (k := k) (Pi.single H 1 : ι → k) 0 = 0 := by
    apply Subtype.ext
    simp
  simp only [hz, hw, Finset.sum_const_zero, smul_zero]

end ChenRanks.Koszul
