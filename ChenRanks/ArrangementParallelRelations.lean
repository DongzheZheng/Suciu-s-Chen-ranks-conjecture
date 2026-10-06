import ChenRanks.AffinePivotQuotient

/-!
# Actual affine parallel-pair relations

Parallel pairs are genuine quadratic relations for an affine arrangement.
The constant offset term is retained throughout: normal dependence alone
does not justify an affine triple relation. The pair identity follows from
the actual universal derivation of the actual two rational functions.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

section RationalPair

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- An actual constant affine relation between two nonzero functions
forces their actual logarithmic exterior product to vanish. -/
theorem logarithmic_affine_pair_relation (u v : Fˣ) (a b : k)
    (hv : (v : F) = algebraMap k F a * (u : F) + algebraMap k F b) :
    exteriorWedge (k := F) (logarithmicDifferential k F u)
      (logarithmicDifferential k F v) = 0 := by
  have hD : KaehlerDifferential.D k F (v : F) =
      algebraMap k F a • KaehlerDifferential.D k F (u : F) := by
    rw [hv]
    simp [Derivation.leibniz]
  simp only [logarithmicDifferential, hD, wedge_smul_left,
    wedge_smul_right, wedge_self, smul_zero]

end RationalPair

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance arrangementParallelRelationsDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The actual polynomial relation of a parallel pair includes the
original affine offsets. -/
theorem equationPolynomial_affine_relation_of_parallel (H K : ι) (c : ℂ)
    (hc : A.normal K = c • A.normal H) :
    A.equationPolynomial K = MvPolynomial.C c * A.equationPolynomial H +
      MvPolynomial.C (c * A.offset H - A.offset K) := by
  classical
  have hn (i : Fin d) : A.normal K (Pi.single i 1) =
      c * A.normal H (Pi.single i 1) := by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using
      DFunLike.congr_fun hc (Pi.single i 1)
  have hs : (∑ i : Fin d,
      MvPolynomial.C (A.normal K (Pi.single i 1)) * MvPolynomial.X i) =
      MvPolynomial.C c * (∑ i : Fin d,
        MvPolynomial.C (A.normal H (Pi.single i 1)) * MvPolynomial.X i) := by
    simp only [hn, map_mul, Finset.mul_sum, mul_assoc]
  simp only [equationPolynomial, hs, map_sub, map_mul]
  ring

/-- The same actual affine relation in the original rational-function field. -/
theorem equationFunction_affine_relation_of_parallel (H K : ι) (c : ℂ)
    (hc : A.normal K = c • A.normal H) :
    A.equationFunction K =
      algebraMap ℂ (RationalFunctionField (d := d)) c * A.equationFunction H +
        algebraMap ℂ (RationalFunctionField (d := d))
          (c * A.offset H - A.offset K) := by
  simp only [equationFunction, A.equationPolynomial_affine_relation_of_parallel H K c hc,
    map_add, map_mul]
  rfl

/-- Restriction to the actual hyperplane of the first member of a parallel
pair gives the actual constant affine discrepancy. -/
theorem hyperplanePivotRestriction_parallel (H K : ι) (j : Fin d)
    (hj : A.normal H (Pi.single j 1) ≠ 0) (c : ℂ)
    (hc : A.normal K = c • A.normal H) :
    A.hyperplanePivotRestriction H j (A.equationPolynomial K) =
      MvPolynomial.C (c * A.offset H - A.offset K) := by
  rw [A.equationPolynomial_affine_relation_of_parallel H K c hc, map_add, map_mul,
    A.hyperplanePivotRestriction_equation H j hj]
  simp only [mul_zero, zero_add]
  exact (A.hyperplanePivotRestriction H j).commutes _

/-- Every other actual equation restricts to a nonzero polynomial, by the
already computed actual restriction kernel and original distinctness. -/
theorem hyperplanePivotRestriction_other_ne_zero (H K : ι) (hHK : H ≠ K)
    (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0) :
    A.hyperplanePivotRestriction H j (A.equationPolynomial K) ≠ 0 := by
  intro hz
  apply A.equationPolynomial_not_mem_hyperplanePrimeIdeal H K hHK
  rw [← A.hyperplanePivotRestriction_ker H j hj]
  exact hz

/-- In a distinct parallel pair the actual affine discrepancy is nonzero. -/
theorem parallel_offset_discrepancy_ne_zero (H K : ι) (hHK : H ≠ K) (c : ℂ)
    (hc : A.normal K = c • A.normal H) : c * A.offset H - A.offset K ≠ 0 := by
  obtain ⟨j, hj⟩ := A.exists_hyperplanePivot H
  intro hz
  have h := A.hyperplanePivotRestriction_other_ne_zero H K hHK j hj
  rw [A.hyperplanePivotRestriction_parallel H K j hj c hc, hz, map_zero] at h
  exact h rfl

/-- The genuine affine parallel-pair generator is in the actual rational
quadratic kernel. No artificial triple at infinity is supplied as input. -/
theorem parallelPair_mem_rationalQuadraticKernel (H K : ι) (c : ℂ)
    (hc : A.normal K = c • A.normal H) :
    exteriorWedge (k := ℂ) (Pi.single H 1) (Pi.single K 1) ∈
      A.rationalQuadraticKernel := by
  rw [A.exteriorWedge_mem_rationalQuadraticKernel_iff,
    A.logarithmicRealization_basis, A.logarithmicRealization_basis]
  exact logarithmic_affine_pair_relation (A.equationUnit H) (A.equationUnit K)
    c (c * A.offset H - A.offset K)
    (A.equationFunction_affine_relation_of_parallel H K c hc)

end AffineArrangement

end ChenRanks
