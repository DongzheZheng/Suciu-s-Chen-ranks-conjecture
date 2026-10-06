import ChenRanks.KoszulQuotientGrading
import ChenRanks.KoszulBinomialIdentity

/-!
# Homogeneous dimensions of zero-relation Koszul modules

In symmetric-algebra coordinates, every positive-degree monomial has a
preimage under the restricted multiplication map. The homogeneous cycle
space is its kernel, whose dimension follows from rank-nullity. Zero
quadratic relations give the zero relation map by tensor induction.

The resulting dimension formula applies also in dimensions zero and one
and computes the corresponding homogeneous image in the quotient.
-/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)

/-- Restriction of the original multiplication differential to its genuine
coefficient-degree subspace, with its original codomain retained. -/
def multiplicationDegreeToS (r : ℕ) :
    c1Degree k V b (r + 1) →ₗ[k] S k V :=
  (delta1 k V).restrictScalars k ∘ₗ (c1Degree k V b (r + 1)).subtype

/-- Every monomial of the required positive degree has an actual
multiplication preimage; existence of a variable follows from its degree. -/
theorem homogeneous_monomial_mem_multiplication_range (r : ℕ)
    (d : ι →₀ ℕ) (c : k) (hd : d.degree = r + 2) :
    (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial d c) ∈
      LinearMap.range (multiplicationDegreeToS k V b r) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : d = 0 := Finsupp.ext h
    simp [hz] at hd
  let f : ι →₀ ℕ := d - Finsupp.single i 1
  have hadd : f + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
  have hf : f.degree = r + 1 := by
    have hh := congrArg Finsupp.degree hadd
    simp only [map_add, Finsupp.degree_single] at hh
    omega
  let e := SymmetricAlgebra.equivMvPolynomial b
  let s : S k V := e.symm (MvPolynomial.monomial f c)
  have hs : s ∈ homogeneousS k V b (r + 1) := by
    change MvPolynomial.IsHomogeneous (e s) (r + 1)
    simpa only [s, AlgEquiv.apply_symm_apply] using
      MvPolynomial.isHomogeneous_monomial c hf
  refine ⟨⟨s ⊗ₜ[k] b i,
    tmul_mem_tensorHomogeneous k V b V (r + 1) s hs (b i)⟩, ?_⟩
  change s * SymmetricAlgebra.ι k V (b i) = e.symm (MvPolynomial.monomial d c)
  apply e.injective
  rw [map_mul, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  change e (e.symm (MvPolynomial.monomial f c)) * MvPolynomial.X i =
    e (e.symm (MvPolynomial.monomial d c))
  rw [e.apply_symm_apply, e.apply_symm_apply]
  simpa only [pow_one, hadd] using
    (MvPolynomial.monomial_add_single (s := f) (n := i) (e := 1) (a := c)).symm

variable [Fintype ι]

/-- The original multiplication map, with codomain its proved actual
homogeneous target. -/
def multiplicationDegree (r : ℕ) :
    c1Degree k V b (r + 1) →ₗ[k] homogeneousS k V b (r + 2) :=
  (multiplicationDegreeToS k V b r).codRestrict (homogeneousS k V b (r + 2))
    (fun z ↦ delta1_preserves_degree k V b (r + 1) z.property)

@[simp] theorem multiplicationDegree_coe (r : ℕ) (z : c1Degree k V b (r + 1)) :
    (multiplicationDegree k V b r z : S k V) = delta1 k V z := rfl

/-- Actual homogeneous multiplication is surjective.  The proof uses the
finite monomial expansion of the target, rather than an exactness premise. -/
theorem multiplicationDegree_surjective (r : ℕ) :
    Function.Surjective (multiplicationDegree k V b r) := by
  classical
  intro t
  let e := SymmetricAlgebra.equivMvPolynomial b
  let p : MvPolynomial ι k := e (t : S k V)
  have hp : MvPolynomial.IsHomogeneous p (r + 2) := t.property
  have hsum : (t : S k V) =
      ∑ d ∈ p.support, e.symm (MvPolynomial.monomial d (p.coeff d)) := by
    apply e.injective
    simp only [map_sum, AlgEquiv.apply_symm_apply]
    exact MvPolynomial.as_sum p
  have ht : (t : S k V) ∈ LinearMap.range (multiplicationDegreeToS k V b r) := by
    rw [hsum]
    apply (LinearMap.range (multiplicationDegreeToS k V b r)).sum_mem
    intro d hd
    have hdegree : d.degree = r + 2 := by
      simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hd).symm
    exact homogeneous_monomial_mem_multiplication_range k V b r d (p.coeff d) hdegree
  obtain ⟨z, hz⟩ := ht
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact hz

/-- The original homogeneous cycle intersection is explicitly equivalent
to the kernel of the actual restricted multiplication map. -/
def cycleDegreeEquivKernel (r : ℕ) :
    cycleDegree k V b r ≃ₗ[k] LinearMap.ker (multiplicationDegree k V b r) where
  toFun z := ⟨⟨z.val, z.property.1⟩, by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact LinearMap.mem_ker.mp z.property.2⟩
  invFun y := ⟨y.val.val, ⟨y.val.property, by
    change delta1 k V y.val.val = 0
    exact congrArg Subtype.val (LinearMap.mem_ker.mp y.property)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Rank-nullity for the actual homogeneous multiplication map, using the
proved monomial count and proved surjectivity. -/
theorem cycleDegree_rank_nullity (r : ℕ) :
    Nat.multichoose (Fintype.card ι) (r + 2) +
        _root_.Module.finrank k (cycleDegree k V b r) =
      Nat.multichoose (Fintype.card ι) (r + 1) * Fintype.card ι := by
  letI : FiniteDimensional k V :=
    FiniteDimensional.of_injective b.repr.toLinearMap b.repr.injective
  have h := (multiplicationDegree k V b r).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (multiplicationDegree_surjective k V b r),
    _root_.finrank_top, ← (cycleDegreeEquivKernel k V b r).finrank_eq,
    homogeneousS_finrank k V b (r + 2)] at h
  have hc := tensorHomogeneous_finrank k V b V (r + 1)
  rw [_root_.Module.finrank_eq_card_basis b] at hc
  rw [hc] at h
  exact h

/-- The actual homogeneous cycle dimension, with no positive-dimension
assumption and no natural-number subtraction. -/
theorem cycleDegree_finrank (r : ℕ) :
    _root_.Module.finrank k (cycleDegree k V b r) =
      (r + 1) * (Fintype.card ι + r).choose (r + 2) := by
  have h := cycleDegree_rank_nullity k V b r
  have hnum := zero_relation_multichoose_identity (Fintype.card ι) r
  rw [Nat.mul_comm] at h
  omega

/-- Restricting the actual second differential to the zero quadratic
submodule gives the zero map, by genuine tensor induction. -/
theorem relationDegree_bot (r : ℕ) :
    relationDegree k V b (⊥ : Submodule k (⋀[k]^2 V)) r = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (relationDegree k V b (⊥ : Submodule k (⋀[k]^2 V)) r x : C1 k V) = 0
  induction x with
  | zero => simp
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  | tmul s w =>
    have hw : (w : ⋀[k]^2 V) = 0 := (Submodule.mem_bot k).mp w.property
    change delta2 k V ((s : S k V) ⊗ₜ[k] (w : ⋀[k]^2 V)) = 0
    rw [hw, TensorProduct.tmul_zero, map_zero]

/-- The zero-relation homogeneous quotient is genuinely equivalent to its
actual homogeneous cycles. -/
def homogeneousModuleZeroEquivCycles (r : ℕ) :
    homogeneousModule k V b (⊥ : Submodule k (⋀[k]^2 V)) r ≃ₗ[k]
      cycleDegree k V b r :=
  (LinearMap.range (relationDegree k V b (⊥ : Submodule k (⋀[k]^2 V)) r)).quotEquivOfEqBot
    (by rw [relationDegree_bot, LinearMap.range_zero])

/-- The manuscript's free Koszul-piece formula for the actual quotient. -/
theorem homogeneousModule_zero_finrank (r : ℕ) :
    _root_.Module.finrank k
        (homogeneousModule k V b (⊥ : Submodule k (⋀[k]^2 V)) r) =
      (r + 1) * (Fintype.card ι + r).choose (r + 2) := by
  rw [(homogeneousModuleZeroEquivCycles k V b r).finrank_eq,
    cycleDegree_finrank k V b r]

/-- The same formula using the actual ambient vector-space dimension. -/
theorem homogeneousModule_zero_finrank_dimension (r : ℕ) :
    _root_.Module.finrank k
        (homogeneousModule k V b (⊥ : Submodule k (⋀[k]^2 V)) r) =
      (r + 1) * (_root_.Module.finrank k V + r).choose (r + 2) := by
  rw [_root_.Module.finrank_eq_card_basis b]
  exact homogeneousModule_zero_finrank k V b r

/-- The proved degreewise equivalence transfers the formula to the actual
degree-image in the original ungraded Koszul quotient. -/
theorem originalDegree_zero_finrank (r : ℕ) :
    _root_.Module.finrank k
        (LinearMap.range
          (degreeCycleToUngraded k V b (⊥ : Submodule k (⋀[k]^2 V)) r)) =
      (r + 1) * (_root_.Module.finrank k V + r).choose (r + 2) := by
  rw [← (homogeneousModuleEquivOriginalDegree k V b
    (⊥ : Submodule k (⋀[k]^2 V)) r).finrank_eq]
  exact homogeneousModule_zero_finrank_dimension k V b r

end ChenRanks.Koszul
