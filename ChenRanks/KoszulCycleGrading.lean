import ChenRanks.KoszulFree

/-!
# Finite grading of the actual Koszul cycles

Coefficient projection commutes with the actual multiplication differential.
The actual coefficient-degree-zero multiplication map is proved surjective
in monomial coordinates and injective by its proved dimensions.  Therefore
its cycles vanish.  Every original cycle has a finite decomposition into the
actual shifted homogeneous cycle subspaces.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

theorem homogeneousProjection_eq_zero_of_totalDegree_lt (s : S k V) (n : ℕ)
    (hn : (SymmetricAlgebra.equivMvPolynomial b s).totalDegree < n) :
    homogeneousProjection k V b n s = 0 := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  rw [polynomial_homogeneousProjection, map_zero]
  exact MvPolynomial.homogeneousComponent_eq_zero n
    (SymmetricAlgebra.equivMvPolynomial b s) hn

/-- The true homogeneous expansion remains valid at every sufficiently
large finite cutoff. -/
theorem sum_homogeneousProjection_of_le (s : S k V) (N : ℕ)
    (hN : (SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1 ≤ N) :
    (∑ n ∈ Finset.range N, homogeneousProjection k V b n s) = s := by
  have hz : ∀ n ≥ (SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1,
      homogeneousProjection k V b n s = 0 := by
    intro n hn
    exact homogeneousProjection_eq_zero_of_totalDegree_lt k V b s n (by omega)
  rw [Finset.eventually_constant_sum hz hN, sum_homogeneousProjection]

/-- Every original tensor has an actual finite coefficient-degree
decomposition, valid at all larger cutoffs. -/
theorem exists_tensorProjection_cutoff (W : Type*) [AddCommGroup W] [_root_.Module k W]
    (x : S k V ⊗[k] W) :
    ∃ N : ℕ, ∀ M ≥ N, (∑ n ∈ Finset.range M, tensorProjection k V b W n x) = x := by
  induction x with
  | zero => exact ⟨0, fun _ _ ↦ by simp⟩
  | add x y hx hy =>
    obtain ⟨Nx, hx⟩ := hx
    obtain ⟨Ny, hy⟩ := hy
    refine ⟨max Nx Ny, ?_⟩
    intro M hM
    simp only [map_add, Finset.sum_add_distrib,
      hx M ((le_max_left Nx Ny).trans hM), hy M ((le_max_right Nx Ny).trans hM)]
  | tmul s w =>
    refine ⟨(SymmetricAlgebra.equivMvPolynomial b s).totalDegree + 1, ?_⟩
    intro M hM
    simp only [tensorProjection_tmul]
    rw [← TensorProduct.sum_tmul, sum_homogeneousProjection_of_le k V b s M hM]

variable [Fintype ι]

/-- The actual first differential commutes with coefficient projection,
with its genuine degree shift. -/
theorem delta1_projection_commutes (n : ℕ) :
    (delta1 k V).restrictScalars k ∘ₗ tensorProjection k V b V n =
      homogeneousProjection k V b (n + 1) ∘ₗ (delta1 k V).restrictScalars k := by
  apply TensorProduct.ext'
  intro s v
  change homogeneousProjection k V b n s * SymmetricAlgebra.ι k V v =
    homogeneousProjection k V b (n + 1) (s * SymmetricAlgebra.ι k V v)
  exact (homogeneousProjection_mul_of_homogeneous k V b n 1 s
    (SymmetricAlgebra.ι k V v) (homogeneousS_ι k V b v)).symm

/-- Multiplication in every actual coefficient degree, including zero. -/
def multiplicationAtDegree (n : ℕ) :
    c1Degree k V b n →ₗ[k] homogeneousS k V b (n + 1) :=
  (((delta1 k V).restrictScalars k).comp (c1Degree k V b n).subtype).codRestrict
    (homogeneousS k V b (n + 1)) (fun z ↦ delta1_preserves_degree k V b n z.property)

/-- The positive-degree monomial construction also proves surjectivity
at coefficient degree zero, without assuming a nonempty basis. -/
theorem multiplicationAtDegree_surjective (n : ℕ) :
    Function.Surjective (multiplicationAtDegree k V b n) := by
  classical
  let e := SymmetricAlgebra.equivMvPolynomial b
  have hm : ∀ (d : ι →₀ ℕ) (c : k), d.degree = n + 1 →
      ∃ z : c1Degree k V b n, delta1 k V z = e.symm (MvPolynomial.monomial d c) := by
    intro d c hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      have hz : d = 0 := Finsupp.ext h
      simp [hz] at hd
    let f : ι →₀ ℕ := d - Finsupp.single i 1
    have hadd : f + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
    have hf : f.degree = n := by
      have hh := congrArg Finsupp.degree hadd
      simp only [map_add, Finsupp.degree_single] at hh
      omega
    let s : S k V := e.symm (MvPolynomial.monomial f c)
    have hs : s ∈ homogeneousS k V b n := by
      change MvPolynomial.IsHomogeneous (e s) n
      simpa only [s, AlgEquiv.apply_symm_apply] using MvPolynomial.isHomogeneous_monomial c hf
    refine ⟨⟨s ⊗ₜ[k] b i, tmul_mem_tensorHomogeneous k V b V n s hs (b i)⟩, ?_⟩
    change s * SymmetricAlgebra.ι k V (b i) = e.symm (MvPolynomial.monomial d c)
    apply e.injective
    rw [map_mul, SymmetricAlgebra.equivMvPolynomial_ι_apply]
    change e (e.symm (MvPolynomial.monomial f c)) * MvPolynomial.X i =
      e (e.symm (MvPolynomial.monomial d c))
    rw [e.apply_symm_apply, e.apply_symm_apply]
    simpa only [pow_one, hadd] using
      (MvPolynomial.monomial_add_single (s := f) (n := i) (e := 1) (a := c)).symm
  intro t
  let p : MvPolynomial ι k := e (t : S k V)
  have hp : MvPolynomial.IsHomogeneous p (n + 1) := t.property
  have hsum : (t : S k V) =
      ∑ d ∈ p.support, e.symm (MvPolynomial.monomial d (p.coeff d)) := by
    apply e.injective
    simp only [map_sum, AlgEquiv.apply_symm_apply]
    exact MvPolynomial.as_sum p
  let f : c1Degree k V b n →ₗ[k] S k V :=
    (delta1 k V).restrictScalars k ∘ₗ (c1Degree k V b n).subtype
  have ht : (t : S k V) ∈ LinearMap.range f := by
    rw [hsum]
    apply (LinearMap.range f).sum_mem
    intro d hd
    apply hm d (p.coeff d)
    simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hd).symm
  obtain ⟨z, hz⟩ := ht
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact hz

/-- Actual coefficient-degree-zero multiplication is injective, since
its actual source and target dimensions coincide and it is surjective. -/
theorem multiplicationAtDegree_zero_injective :
    Function.Injective (multiplicationAtDegree k V b 0) := by
  letI : FiniteDimensional k V :=
    FiniteDimensional.of_injective b.repr.toLinearMap b.repr.injective
  have hdim : _root_.Module.finrank k (c1Degree k V b 0) =
      _root_.Module.finrank k (homogeneousS k V b 1) := by
    rw [tensorHomogeneous_finrank k V b V 0, homogeneousS_finrank k V b 1,
      _root_.Module.finrank_eq_card_basis b]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    (multiplicationAtDegree_surjective k V b 0)

/-- There is no nonzero actual Koszul cycle of coefficient degree zero. -/
theorem coefficient_zero_cycle_eq_zero (x : C1 k V)
    (hx : x ∈ c1Degree k V b 0) (hz : delta1 k V x = 0) : x = 0 := by
  let z : c1Degree k V b 0 := ⟨x, hx⟩
  have hz' : multiplicationAtDegree k V b 0 z = 0 := by
    apply Subtype.ext
    exact hz
  have h := multiplicationAtDegree_zero_injective k V b
    (show multiplicationAtDegree k V b 0 z = multiplicationAtDegree k V b 0 0 by
      rw [hz', map_zero])
  exact congrArg Subtype.val h

/-- The actual coefficient projection of an original cycle remains a
cycle, so its shifted codomain is the actual cycle intersection. -/
def cycleProjection (r : ℕ) :
    LinearMap.ker (delta1 k V) →ₗ[k] cycleDegree k V b r :=
  ((tensorProjection k V b V (r + 1)).comp
    ((LinearMap.ker (delta1 k V)).subtype.restrictScalars k)).codRestrict
      (cycleDegree k V b r) (fun z ↦ ⟨tensorProjection_mem k V b V (r + 1) z, by
        change delta1 k V (tensorProjection k V b V (r + 1) z) = 0
        have h := DFunLike.congr_fun (delta1_projection_commutes k V b (r + 1)) z.val
        change delta1 k V (tensorProjection k V b V (r + 1) z) =
          homogeneousProjection k V b (r + 1 + 1) (delta1 k V z) at h
        rw [LinearMap.mem_ker.mp z.property, map_zero] at h
        exact h⟩)

@[simp] theorem cycleProjection_coe (r : ℕ) (z : LinearMap.ker (delta1 k V)) :
    (cycleProjection k V b r z : C1 k V) = tensorProjection k V b V (r + 1) z := rfl

/-- Every original cycle has a genuine finite decomposition into the
positive coefficient degrees corresponding to the manuscript's `r ≥ 0`. -/
theorem exists_sum_cycleProjection (z : LinearMap.ker (delta1 k V)) :
    ∃ N : ℕ, (∑ r ∈ Finset.range N,
      degreeCycleInclusion k V b r (cycleProjection k V b r z)) = z := by
  obtain ⟨N, hN⟩ := exists_tensorProjection_cutoff k V b V z.val
  refine ⟨N, ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ r ∈ Finset.range N, tensorProjection k V b V (r + 1) z) = z.val
  have hzero : tensorProjection k V b V 0 z = 0 := by
    apply coefficient_zero_cycle_eq_zero k V b
      (tensorProjection k V b V 0 z) (tensorProjection_mem k V b V 0 z)
    have h := DFunLike.congr_fun (delta1_projection_commutes k V b 0) z.val
    change delta1 k V (tensorProjection k V b V 0 z) =
      homogeneousProjection k V b 1 (delta1 k V z) at h
    rw [LinearMap.mem_ker.mp z.property, map_zero] at h
    exact h
  have h := hN (N + 1) (by omega)
  rw [Finset.sum_range_succ', hzero, add_zero] at h
  exact h

end ChenRanks.Koszul
