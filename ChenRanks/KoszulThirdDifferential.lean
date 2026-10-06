import ChenRanks.KoszulThirdChain
import ChenRanks.KoszulPolynomialHomotopy

/-!
# The genuine second Koszul homotopy and second-degree exactness

The genuine third differential is constructed in `KoszulThirdChain`.
Actual polynomial derivatives yield `G₁ δ₂ + δ₃ G₂ = (n + 2) id` in
coefficient degree `n`.  Actual finite tensor expansions then prove global
exactness in characteristic zero, without an exactness premise.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

variable {ι : Type*} (b : _root_.Module.Basis ι k V) [Fintype ι]

/-- The genuine coefficient-degree subspace in the third tensor module. -/
abbrev c3Degree (n : ℕ) := tensorHomogeneous k V b (⋀[k]^3 V) n

/-- The second derivative homotopy before its actual tensor descent. -/
def homotopyTwoBilinear : S k V →ₗ[k] (⋀[k]^2 V) →ₗ[k] C3 k V :=
  LinearMap.mk₂ k
    (fun s w ↦ ∑ i, symmetricPartial k V b i s ⊗ₜ[k] exteriorInsert k V (b i) w)
    (by intro s t w; simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib])
    (by intro c s w; simp only [map_smul, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, Finset.smul_sum])
    (by intro s v w; simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib])
    (by intro c s w; simp only [map_smul, TensorProduct.tmul_smul, Finset.smul_sum])

def homotopyTwo : C2 k V →ₗ[k] C3 k V := TensorProduct.lift (homotopyTwoBilinear k V b)

@[simp] theorem homotopyTwo_tmul (s : S k V) (w : ⋀[k]^2 V) :
    homotopyTwo k V b (s ⊗ₜ[k] w) =
      ∑ i, symmetricPartial k V b i s ⊗ₜ[k] exteriorInsert k V (b i) w := rfl

theorem homotopyTwo_preserves_degree (n : ℕ) :
    c2Degree k V b n ≤ (c3Degree k V b (n - 1)).comap (homotopyTwo k V b) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, w, rfl⟩
  change homotopyTwo k V b (s ⊗ₜ[k] w) ∈ c3Degree k V b (n - 1)
  rw [homotopyTwo_tmul]
  exact (c3Degree k V b (n - 1)).sum_mem fun i _ ↦
    tmul_mem_tensorHomogeneous k V b (⋀[k]^3 V) (n - 1) _
      (symmetricPartial_preserves_degree k V b i hs) (exteriorInsert k V (b i) w)

/-- Product-rule expansion of the already constructed genuine first homotopy. -/
theorem homotopyOne_mul_generator (s : S k V) (u v : V) :
    homotopyOne k V b ((s * SymmetricAlgebra.ι k V u) ⊗ₜ[k] v) =
      (∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V u) ⊗ₜ[k]
        exteriorWedge (b i) v) + s ⊗ₜ[k] exteriorWedge u v := by
  rw [homotopyOne_tmul]
  simp only [symmetricPartial_mul, symmetricPartial_ι, TensorProduct.add_tmul,
    Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i, (s * (b.repr u i • (1 : S k V))) ⊗ₜ[k] exteriorWedge (b i) v) =
        ∑ i, s ⊗ₜ[k] exteriorWedge (b.repr u i • b i) v := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_smul_comm, mul_one, TensorProduct.smul_tmul,
        ← exteriorWedgeBilin_apply, map_smul, LinearMap.smul_apply]
    _ = s ⊗ₜ[k] exteriorWedge (∑ i, b.repr u i • b i) v := by
      simp only [← exteriorWedgeBilin_apply, map_sum, LinearMap.sum_apply,
        TensorProduct.tmul_sum]
    _ = s ⊗ₜ[k] exteriorWedge u v := by rw [b.sum_repr]

theorem delta3_homotopyTwo_wedge (s : S k V) (u v : V) :
    delta3 k V (homotopyTwo k V b (s ⊗ₜ[k] exteriorWedge u v)) =
      (∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V (b i)) ⊗ₜ[k]
        exteriorWedge u v) -
      (∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V u) ⊗ₜ[k]
        exteriorWedge (b i) v) +
      (∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V v) ⊗ₜ[k]
        exteriorWedge (b i) u) := by
  simp only [homotopyTwo_tmul, exteriorInsert_wedge, map_sum, delta3_tmul,
    delta3Linear_wedge, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, smul_add, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- The genuine second homotopy identity on actual decomposable exterior tensors. -/
theorem polynomial_homotopyTwo_wedge (n : ℕ) (s : S k V)
    (hs : s ∈ homogeneousS k V b n) (u v : V) :
    homotopyOne k V b (delta2 k V (s ⊗ₜ[k] exteriorWedge u v)) +
      delta3 k V (homotopyTwo k V b (s ⊗ₜ[k] exteriorWedge u v)) =
        ((n + 2 : ℕ) : k) • (s ⊗ₜ[k] exteriorWedge u v) := by
  rw [delta2_tmul, delta2Linear_exteriorWedge, smul_sub]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_sub]
  rw [homotopyOne_mul_generator, homotopyOne_mul_generator,
    delta3_homotopyTwo_wedge, ← TensorProduct.sum_tmul, symmetricPartial_euler k V b s hs,
    wedgeTwo_swap k V v u]
  simp only [TensorProduct.tmul_neg, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, TensorProduct.add_tmul,
    Nat.cast_add, Nat.cast_ofNat, add_smul, two_smul]
  abel

/-- Actual exterior spanning extends the same identity to every exterior tensor. -/
theorem polynomial_homotopyTwo_tmul (n : ℕ) (s : S k V)
    (hs : s ∈ homogeneousS k V b n) (w : ⋀[k]^2 V) :
    homotopyOne k V b (delta2 k V (s ⊗ₜ[k] w)) +
      delta3 k V (homotopyTwo k V b (s ⊗ₜ[k] w)) =
        ((n + 2 : ℕ) : k) • (s ⊗ₜ[k] w) := by
  let T : (⋀[k]^2 V) →ₗ[k] C2 k V :=
    ((homotopyOne k V b).comp ((delta2 k V).restrictScalars k) +
      ((delta3 k V).restrictScalars k).comp (homotopyTwo k V b) -
        ((n + 2 : ℕ) : k) • LinearMap.id).comp
          (TensorProduct.mk k (S k V) (⋀[k]^2 V) s)
  have hT : T = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change homotopyOne k V b (delta2 k V (s ⊗ₜ[k] exteriorPower.ιMulti k 2 a)) +
      delta3 k V (homotopyTwo k V b (s ⊗ₜ[k] exteriorPower.ιMulti k 2 a)) -
        ((n + 2 : ℕ) : k) • (s ⊗ₜ[k] exteriorPower.ιMulti k 2 a) = 0
    have ha : exteriorPower.ιMulti k 2 a = exteriorWedge (a 0) (a 1) := by
      change exteriorPower.ιMulti k 2 a = exteriorPower.ιMulti k 2 ![a 0, a 1]
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [ha, polynomial_homotopyTwo_wedge k V b n s hs, sub_self]
  have h := DFunLike.congr_fun hT w
  change homotopyOne k V b (delta2 k V (s ⊗ₜ[k] w)) +
    delta3 k V (homotopyTwo k V b (s ⊗ₜ[k] w)) -
      ((n + 2 : ℕ) : k) • (s ⊗ₜ[k] w) = 0 at h
  exact sub_eq_zero.mp h

/-- The genuine second homotopy identity on arbitrary homogeneous tensors. -/
theorem polynomial_homotopyTwo_degree (n : ℕ) (z : C2 k V)
    (hz : z ∈ c2Degree k V b n) :
    homotopyOne k V b (delta2 k V z) + delta3 k V (homotopyTwo k V b z) =
      ((n + 2 : ℕ) : k) • z := by
  let T : C2 k V →ₗ[k] C2 k V :=
    (homotopyOne k V b).comp ((delta2 k V).restrictScalars k) +
      ((delta3 k V).restrictScalars k).comp (homotopyTwo k V b) -
        ((n + 2 : ℕ) : k) • LinearMap.id
  have hle : c2Degree k V b n ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, w, rfl⟩
    change homotopyOne k V b (delta2 k V (s ⊗ₜ[k] w)) +
      delta3 k V (homotopyTwo k V b (s ⊗ₜ[k] w)) -
        ((n + 2 : ℕ) : k) • (s ⊗ₜ[k] w) = 0
    rw [polynomial_homotopyTwo_tmul k V b n s hs w, sub_self]
  have h := hle hz
  change homotopyOne k V b (delta2 k V z) + delta3 k V (homotopyTwo k V b z) -
    ((n + 2 : ℕ) : k) • z = 0 at h
  exact sub_eq_zero.mp h

variable [CharZero k]

theorem homogeneous_delta2_cycle_preimage (n : ℕ) (z : C2 k V)
    (hz : z ∈ c2Degree k V b n) (hcycle : delta2 k V z = 0) :
    ∃ y : C3 k V, y ∈ c3Degree k V b (n - 1) ∧ delta3 k V y = z := by
  let c : k := ((n + 2 : ℕ) : k)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (show n + 2 ≠ 0 by omega)
  have he := polynomial_homotopyTwo_degree k V b n z hz
  rw [hcycle, map_zero, zero_add] at he
  refine ⟨c⁻¹ • homotopyTwo k V b z, ?_, ?_⟩
  · exact (c3Degree k V b (n - 1)).smul_mem c⁻¹
      (homotopyTwo_preserves_degree k V b n hz)
  · change (delta3 k V).restrictScalars k (c⁻¹ • homotopyTwo k V b z) = z
    rw [map_smul]
    change c⁻¹ • delta3 k V (homotopyTwo k V b z) = z
    rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul]

include b in
/-- Exactness in the genuine second tensor term follows from actual homogeneous
preimages and the proved finite tensor expansion; no exactness premise is used. -/
theorem delta3_range_eq_delta2_ker :
    LinearMap.range (delta3 k V) = LinearMap.ker (delta2 k V) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact DFunLike.congr_fun (delta2_comp_delta3 k V) y
  · intro z hz
    obtain ⟨N, hN⟩ := exists_tensorProjection_cutoff k V b (⋀[k]^2 V) z
    rw [← hN N le_rfl]
    apply (LinearMap.range (delta3 k V)).sum_mem
    intro n _
    have hcycle : delta2 k V (tensorProjection k V b (⋀[k]^2 V) n z) = 0 := by
      have he := DFunLike.congr_fun (delta2_projection_commutes k V b n) z
      have hz0 : delta2 k V z = 0 := LinearMap.mem_ker.mp hz
      simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hz0, map_zero]
        using he.symm
    obtain ⟨y, _, hy⟩ := homogeneous_delta2_cycle_preimage k V b n
      (tensorProjection k V b (⋀[k]^2 V) n z) (tensorProjection_mem k V b _ n z) hcycle
    exact ⟨y, hy⟩

omit [Fintype ι] in
/-- Canonical exactness without a basis input, obtained using the actual finite basis. -/
theorem delta3_exact [FiniteDimensional k V] :
    LinearMap.range (delta3 k V) = LinearMap.ker (delta2 k V) :=
  delta3_range_eq_delta2_ker k V (_root_.Module.finBasis k V)

end ChenRanks.Koszul
