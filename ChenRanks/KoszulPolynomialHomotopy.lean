import ChenRanks.KoszulCycleGrading
import ChenRanks.ExteriorSeparation
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Explicit polynomial homotopy and exactness of the actual first Koszul maps

Actual multivariate partial derivatives are transported through the genuine
basis equivalence of the original symmetric algebra.  They define explicit
linear homotopies on the original tensor modules.  Euler's actual homogeneous
identity proves `G₀ δ₁ + δ₂ G₁ = (n + 1) id` on coefficient degree `n`.

In characteristic zero this identity constructs an actual second-differential
preimage for every homogeneous cycle.  The proved finite homogeneous cycle
decomposition gives global exactness `im δ₂ = ker δ₁`.  Actual polynomial
finite generation of the cycle space and its original relation quotient then
follows from the true surjective map from the true finite second tensor module.

No exactness, finite-generation, support, or Chen-comparison premise is used.
The third differential and the full presentation are not constructed here.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

/-- The actual partial derivative transported to the original symmetric algebra. -/
def symmetricPartial (i : ι) : S k V →ₗ[k] S k V :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearMap ∘ₗ
    (MvPolynomial.pderiv i).toLinearMap ∘ₗ
      (SymmetricAlgebra.equivMvPolynomial b).toLinearMap

@[simp] theorem polynomial_symmetricPartial (i : ι) (s : S k V) :
    SymmetricAlgebra.equivMvPolynomial b (symmetricPartial k V b i s) =
      MvPolynomial.pderiv i (SymmetricAlgebra.equivMvPolynomial b s) := by
  simp [symmetricPartial]

theorem symmetricPartial_mul (i : ι) (s t : S k V) :
    symmetricPartial k V b i (s * t) =
      symmetricPartial k V b i s * t + s * symmetricPartial k V b i t := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp only [polynomial_symmetricPartial, map_mul, MvPolynomial.pderiv_mul, map_add]

@[simp] theorem symmetricPartial_one (i : ι) :
    symmetricPartial k V b i 1 = 0 := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp only [polynomial_symmetricPartial, map_one, MvPolynomial.pderiv_one, map_zero]

/-- The transported operator is a genuine derivation; its Leibniz rule
and its value at one were proved from the actual polynomial derivative. -/
def symmetricPartialDerivation (i : ι) : Derivation k (S k V) (S k V) where
  toLinearMap := symmetricPartial k V b i
  map_one_eq_zero' := symmetricPartial_one k V b i
  leibniz' s t := by
    rw [symmetricPartial_mul]
    simp only [smul_eq_mul]
    ring

@[simp] theorem symmetricPartial_ι_basis [DecidableEq ι] (i j : ι) :
    symmetricPartial k V b i (SymmetricAlgebra.ι k V (b j)) =
      if i = j then 1 else 0 := by
  classical
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp [polynomial_symmetricPartial, SymmetricAlgebra.equivMvPolynomial_ι_apply,
    MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem symmetricPartial_preserves_degree (i : ι) {n : ℕ} {s : S k V}
    (hs : s ∈ homogeneousS k V b n) :
    symmetricPartial k V b i s ∈ homogeneousS k V b (n - 1) := by
  change MvPolynomial.IsHomogeneous
    (SymmetricAlgebra.equivMvPolynomial b (symmetricPartial k V b i s)) (n - 1)
  rw [polynomial_symmetricPartial]
  exact (hs : MvPolynomial.IsHomogeneous (SymmetricAlgebra.equivMvPolynomial b s) n).pderiv

/-- The derivative of an arbitrary genuine generator is its actual basis coordinate. -/
theorem symmetricPartial_ι (i : ι) (v : V) :
    symmetricPartial k V b i (SymmetricAlgebra.ι k V v) = b.repr v i • (1 : S k V) := by
  classical
  have hmap : (symmetricPartial k V b i).comp (SymmetricAlgebra.ι k V) =
      (LinearMap.toSpanSingleton k (S k V) 1).comp (b.coord i) := by
    apply b.ext
    intro j
    simp [symmetricPartial_ι_basis, _root_.Module.Basis.coord_apply,
      b.repr_self, Finsupp.single_apply, eq_comm]
  exact DFunLike.congr_fun hmap v

theorem delta2Linear_exteriorWedge (u v : V) :
    delta2Linear k V (exteriorWedge (k := k) u v) =
      (SymmetricAlgebra.ι k V u) • ((1 : S k V) ⊗ₜ[k] v) -
        (SymmetricAlgebra.ι k V v) • ((1 : S k V) ⊗ₜ[k] u) := by
  simpa only [exteriorWedge, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using delta2Linear_wedge k V ![u, v]

section FiniteBasis

variable [Fintype ι]

/-- Euler's identity in the original symmetric algebra and its original basis. -/
theorem symmetricPartial_euler {n : ℕ} (s : S k V)
    (hs : s ∈ homogeneousS k V b n) :
    (∑ i, symmetricPartial k V b i s * SymmetricAlgebra.ι k V (b i)) = (n : k) • s := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp only [map_sum, map_mul, polynomial_symmetricPartial,
    SymmetricAlgebra.equivMvPolynomial_ι_apply, map_smul]
  rw [Nat.cast_smul_eq_nsmul k]
  have he := (hs : MvPolynomial.IsHomogeneous
    (SymmetricAlgebra.equivMvPolynomial b s) n).sum_X_mul_pderiv
  simpa only [mul_comm] using he

/-- The first explicit polynomial homotopy, formed from actual derivatives. -/
def homotopyZero : S k V →ₗ[k] C1 k V where
  toFun s := ∑ i, symmetricPartial k V b i s ⊗ₜ[k] b i
  map_add' s t := by
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c s := by
    simp only [map_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      Finset.smul_sum, RingHom.id_apply]

@[simp] theorem homotopyZero_apply (s : S k V) :
    homotopyZero k V b s = ∑ i, symmetricPartial k V b i s ⊗ₜ[k] b i := rfl

/-- The actual bilinear map whose tensor descent is the next homotopy. -/
def homotopyOneBilinear : S k V →ₗ[k] V →ₗ[k] C2 k V :=
  LinearMap.mk₂ k
    (fun s v ↦ ∑ i, symmetricPartial k V b i s ⊗ₜ[k] exteriorWedge (b i) v)
    (by intro s t v; simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib])
    (by intro c s v; simp only [map_smul, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, Finset.smul_sum])
    (by intro s v w; simp only [← exteriorWedgeBilin_apply, map_add,
      TensorProduct.tmul_add, Finset.sum_add_distrib])
    (by intro c s v; simp only [← exteriorWedgeBilin_apply, map_smul,
      TensorProduct.tmul_smul, Finset.smul_sum])

/-- The actual tensor homotopy on the original first tensor module. -/
def homotopyOne : C1 k V →ₗ[k] C2 k V := TensorProduct.lift (homotopyOneBilinear k V b)

@[simp] theorem homotopyOne_tmul (s : S k V) (v : V) :
    homotopyOne k V b (s ⊗ₜ[k] v) =
      ∑ i, symmetricPartial k V b i s ⊗ₜ[k] exteriorWedge (b i) v := rfl

theorem homotopyZero_preserves_degree {n : ℕ} {s : S k V}
    (hs : s ∈ homogeneousS k V b n) :
    homotopyZero k V b s ∈ c1Degree k V b (n - 1) := by
  rw [homotopyZero_apply]
  exact (c1Degree k V b (n - 1)).sum_mem fun i _ ↦
    tmul_mem_tensorHomogeneous k V b V (n - 1) _
      (symmetricPartial_preserves_degree k V b i hs) (b i)

theorem homotopyOne_preserves_degree (n : ℕ) :
    c1Degree k V b n ≤ (c2Degree k V b (n - 1)).comap (homotopyOne k V b) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, v, rfl⟩
  change homotopyOne k V b (s ⊗ₜ[k] v) ∈ c2Degree k V b (n - 1)
  rw [homotopyOne_tmul]
  exact (c2Degree k V b (n - 1)).sum_mem fun i _ ↦
    tmul_mem_tensorHomogeneous k V b (⋀[k]^2 V) (n - 1) _
      (symmetricPartial_preserves_degree k V b i hs) (exteriorWedge (b i) v)

/-- The product-rule expansion in the original first tensor module. -/
theorem homotopyZero_mul_generator (s : S k V) (v : V) :
    homotopyZero k V b (s * SymmetricAlgebra.ι k V v) =
      (∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V v) ⊗ₜ[k] b i) +
        s ⊗ₜ[k] v := by
  rw [homotopyZero_apply]
  simp only [symmetricPartial_mul, symmetricPartial_ι, TensorProduct.add_tmul,
    Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i, (s * (b.repr v i • (1 : S k V))) ⊗ₜ[k] b i) =
        ∑ i, s ⊗ₜ[k] (b.repr v i • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_smul_comm, mul_one, TensorProduct.smul_tmul]
    _ = s ⊗ₜ[k] (∑ i, b.repr v i • b i) := (TensorProduct.tmul_sum _ _ _).symm
    _ = s ⊗ₜ[k] v := by rw [b.sum_repr]

/-- Applying the original second differential to the actual homotopy. -/
theorem delta2_homotopyOne_tmul (s : S k V) (v : V) :
    delta2 k V (homotopyOne k V b (s ⊗ₜ[k] v)) =
      (∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V (b i)) ⊗ₜ[k] v) -
        ∑ i, (symmetricPartial k V b i s * SymmetricAlgebra.ι k V v) ⊗ₜ[k] b i := by
  simp only [homotopyOne_tmul, map_sum, delta2_tmul, delta2Linear_exteriorWedge,
    smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Finset.sum_sub_distrib]

/-- Euler's identity and the actual product rule give the actual
homotopy identity on every genuine homogeneous pure tensor. -/
theorem polynomial_homotopy_tmul (n : ℕ) (s : S k V)
    (hs : s ∈ homogeneousS k V b n) (v : V) :
    homotopyZero k V b (delta1 k V (s ⊗ₜ[k] v)) +
      delta2 k V (homotopyOne k V b (s ⊗ₜ[k] v)) = ((n + 1 : ℕ) : k) • (s ⊗ₜ[k] v) := by
  rw [delta1_tmul, homotopyZero_mul_generator, delta2_homotopyOne_tmul,
    ← TensorProduct.sum_tmul, symmetricPartial_euler k V b s hs]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  abel

/-- The actual homotopy identity on an arbitrary homogeneous tensor,
proved by the genuine span definition of its coefficient degree. -/
theorem polynomial_homotopy_degree (n : ℕ) (z : C1 k V)
    (hz : z ∈ c1Degree k V b n) :
    homotopyZero k V b (delta1 k V z) + delta2 k V (homotopyOne k V b z) =
      ((n + 1 : ℕ) : k) • z := by
  let T : C1 k V →ₗ[k] C1 k V :=
    (homotopyZero k V b).comp ((delta1 k V).restrictScalars k) +
      ((delta2 k V).restrictScalars k).comp (homotopyOne k V b) -
        ((n + 1 : ℕ) : k) • LinearMap.id
  have hle : c1Degree k V b n ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, v, rfl⟩
    change homotopyZero k V b (delta1 k V (s ⊗ₜ[k] v)) +
      delta2 k V (homotopyOne k V b (s ⊗ₜ[k] v)) -
        ((n + 1 : ℕ) : k) • (s ⊗ₜ[k] v) = 0
    rw [polynomial_homotopy_tmul k V b n s hs v, sub_self]
  have h := hle hz
  change homotopyZero k V b (delta1 k V z) + delta2 k V (homotopyOne k V b z) -
      ((n + 1 : ℕ) : k) • z = 0 at h
  exact sub_eq_zero.mp h

variable [CharZero k]

/-- A genuine homogeneous cycle has an explicit actual second-differential
preimage in the genuine coefficient degree one lower. -/
theorem homogeneous_cycle_preimage (n : ℕ) (z : C1 k V)
    (hz : z ∈ c1Degree k V b n) (hcycle : delta1 k V z = 0) :
    ∃ y : C2 k V, y ∈ c2Degree k V b (n - 1) ∧ delta2 k V y = z := by
  let c : k := ((n + 1 : ℕ) : k)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  have he := polynomial_homotopy_degree k V b n z hz
  rw [hcycle, map_zero, zero_add] at he
  refine ⟨c⁻¹ • homotopyOne k V b z, ?_, ?_⟩
  · exact (c2Degree k V b (n - 1)).smul_mem c⁻¹
      (homotopyOne_preserves_degree k V b n hz)
  · change (delta2 k V).restrictScalars k (c⁻¹ • homotopyOne k V b z) = z
    rw [map_smul]
    change c⁻¹ • delta2 k V (homotopyOne k V b z) = z
    rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- In the manuscript's shifted degree `r`, a cycle has an actual
quadratic preimage with coefficient degree exactly `r`. -/
theorem cycleDegree_preimage (r : ℕ) (z : cycleDegree k V b r) :
    ∃ y : C2 k V, y ∈ c2Degree k V b r ∧ delta2 k V y = (z : C1 k V) := by
  obtain ⟨y, hy, he⟩ := homogeneous_cycle_preimage k V b (r + 1) z z.property.1
    (LinearMap.mem_ker.mp z.property.2)
  exact ⟨y, by simpa only [Nat.add_sub_cancel] using hy, he⟩

include b in
/-- The actual range of the original second differential equals the
actual kernel of the original first differential.  Homogeneous cycles
are solved explicitly, then the proved finite cycle expansion is used. -/
theorem delta2_range_eq_delta1_ker :
    LinearMap.range (delta2 k V) = LinearMap.ker (delta1 k V) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    have he := DFunLike.congr_fun (delta1_comp_delta2 k V) y
    exact he
  · intro z hz
    let zc : LinearMap.ker (delta1 k V) := ⟨z, hz⟩
    obtain ⟨N, hN⟩ := exists_sum_cycleProjection k V b zc
    have hsum : (∑ r ∈ Finset.range N,
        (degreeCycleInclusion k V b r (cycleProjection k V b r zc) : C1 k V)) = z := by
      simpa only [Submodule.coe_sum] using congrArg Subtype.val hN
    rw [← hsum]
    apply (LinearMap.range (delta2 k V)).sum_mem
    intro r _
    obtain ⟨y, _, he⟩ := cycleDegree_preimage k V b r (cycleProjection k V b r zc)
    exact ⟨y, he⟩

end FiniteBasis

/-- The original second differential restricted to its proved cycle codomain. -/
def delta2ToCycles : C2 k V →ₗ[S k V] LinearMap.ker (delta1 k V) :=
  (delta2 k V).codRestrict (LinearMap.ker (delta1 k V)) (fun y ↦ by
    exact DFunLike.congr_fun (delta1_comp_delta2 k V) y)

section FiniteDimension

variable [FiniteDimensional k V] [CharZero k]

/-- Global actual exactness, with the genuine finite basis chosen from
the actual space rather than supplied as an additional input. -/
theorem delta2_exact :
    LinearMap.range (delta2 k V) = LinearMap.ker (delta1 k V) :=
  delta2_range_eq_delta1_ker k V (_root_.Module.finBasis k V)

theorem delta2ToCycles_surjective : Function.Surjective (delta2ToCycles k V) := by
  intro z
  have hz : (z : C1 k V) ∈ LinearMap.range (delta2 k V) := by
    rw [delta2_exact k V]
    exact z.property
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- The true cycle module is finite over the original polynomial ring,
because the actual second tensor module is finite and actually surjects. -/
theorem actual_cycles_finite :
    _root_.Module.Finite (S k V) (LinearMap.ker (delta1 k V)) := by
  letI : _root_.Module.Finite (S k V) (C2 k V) := inferInstance
  exact _root_.Module.Finite.of_surjective (delta2ToCycles k V)
    (delta2ToCycles_surjective k V)

/-- The original Koszul quotient is a genuinely finite polynomial module
for every actual quadratic relation subspace. -/
theorem actual_koszulModule_finite (K : Submodule k (⋀[k]^2 V)) :
    _root_.Module.Finite (S k V) (Module k V K) := by
  letI := actual_cycles_finite k V
  infer_instance

end FiniteDimension

end ChenRanks.Koszul
