import ChenRanks.HyperplaneRestrictedDegrees

/-!
# Actual affine equation pair spans and restricted divisor classes

The pair span is the actual constant-field span of the two original
equation polynomials, retaining their offsets. At a genuinely nonparallel
pair, divisibility of the actual pivot-restricted polynomials is exactly
membership of the original equation in that span. For a different
hyperplane in the span, its span with the first hyperplane is the same
actual span, proved by solving the genuine two-coefficient relation.

The finite family is derived from the actual finite distinct coordinate
pairs. It includes parallel equation spans; identifying its nonparallel
members with actual codimension-two geometric flats remains separate.
No pair-class partition or block decomposition is an input.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance affineEquationPairSpansDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The genuine span of the original two affine equation polynomials. -/
def affineEquationPairSpan (H K : ι) : Submodule ℂ (CoordinateRing (d := d)) :=
  Submodule.span ℂ {A.equationPolynomial H, A.equationPolynomial K}

@[simp]
theorem affineEquationPairSpan_swap (H K : ι) :
    A.affineEquationPairSpan H K = A.affineEquationPairSpan K H := by
  unfold affineEquationPairSpan
  congr 1
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]

/-- At a genuine nonparallel pair, an actual restricted divisor class
is exactly the actual affine equation-span class. -/
theorem hyperplaneRestricted_dvd_iff_mem_affineEquationPairSpan
    (H K M : ι) (j : Fin d) (hj : A.normal H (Pi.single j 1) ≠ 0)
    (hparallel : ¬∃ c : ℂ, A.normal K = c • A.normal H) :
    A.hyperplanePivotRestriction H j (A.equationPolynomial K) ∣
        A.hyperplanePivotRestriction H j (A.equationPolynomial M) ↔
      A.equationPolynomial M ∈ A.affineEquationPairSpan H K := by
  constructor
  · intro hdiv
    obtain ⟨c, hc⟩ := constant_multiple_of_degree_one_dvd
      (A.hyperplanePivotRestriction H j (A.equationPolynomial K))
      (A.hyperplanePivotRestriction H j (A.equationPolynomial M))
      (A.hyperplanePivotRestriction_totalDegree_eq_one_of_not_parallel H K j hj hparallel)
      (A.hyperplanePivotRestriction_equation_totalDegree_le_one H M j) hdiv
    obtain ⟨e, he⟩ := (A.hyperplanePivotRestriction_proportional_iff H K M j hj c).mp hc
    apply Submodule.mem_span_pair.mpr
    refine ⟨e, c, ?_⟩
    simp only [MvPolynomial.smul_eq_C_mul]
    exact (add_comm _ _).trans he.symm
  · intro hmem
    obtain ⟨e, c, he⟩ := Submodule.mem_span_pair.mp hmem
    have hpoly : A.equationPolynomial M = MvPolynomial.C c * A.equationPolynomial K +
        MvPolynomial.C e * A.equationPolynomial H := by
      simpa only [MvPolynomial.smul_eq_C_mul, add_comm] using he.symm
    have hprop := (A.hyperplanePivotRestriction_proportional_iff H K M j hj c).mpr ⟨e, hpoly⟩
    rw [hprop]
    exact dvd_mul_left _ _

/-- A different original equation in a true pair span gives exactly
the same pair span with the first original equation. No dimension
criterion or span equality is a premise. -/
theorem affineEquationPairSpan_eq_of_mem (H K M : ι) (hHM : H ≠ M)
    (hM : A.equationPolynomial M ∈ A.affineEquationPairSpan H K) :
    A.affineEquationPairSpan H M = A.affineEquationPairSpan H K := by
  obtain ⟨b, a, hrel⟩ := Submodule.mem_span_pair.mp hM
  have ha : a ≠ 0 := by
    intro hz
    have hdiv : A.equationPolynomial H ∣ A.equationPolynomial M := by
      rw [← hrel, hz, zero_smul, add_zero, MvPolynomial.smul_eq_C_mul]
      exact dvd_mul_left _ _
    exact A.equationPolynomial_not_dvd_of_ne H M hHM hdiv
  have hK : A.equationPolynomial K ∈ A.affineEquationPairSpan H M := by
    have hs : a • A.equationPolynomial K =
        A.equationPolynomial M - b • A.equationPolynomial H := by
      rw [← hrel]
      abel
    have heq : A.equationPolynomial K =
        a⁻¹ • (A.equationPolynomial M - b • A.equationPolynomial H) := by
      rw [← hs, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [heq]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact Submodule.subset_span (by simp)
    · apply Submodule.smul_mem
      exact Submodule.subset_span (by simp)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Submodule.subset_span (by simp)
    · have hp' : p = A.equationPolynomial M := Set.mem_singleton_iff.mp hp
      exact hp'.symm ▸ hM
  · apply Submodule.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Submodule.subset_span (by simp)
    · have hp' : p = A.equationPolynomial K := Set.mem_singleton_iff.mp hp
      exact hp'.symm ▸ hK

/-- A distinct original pair has a constant direction in its actual
affine equation span exactly when the actual normals are parallel.
The original nonzero affine discrepancy is used in the converse. -/
theorem one_mem_affineEquationPairSpan_iff_parallel (H K : ι) (hHK : H ≠ K) :
    (1 : CoordinateRing (d := d)) ∈ A.affineEquationPairSpan H K ↔
      ∃ c : ℂ, A.normal K = c • A.normal H := by
  constructor
  · intro hmem
    obtain ⟨a, b, hrel⟩ := Submodule.mem_span_pair.mp hmem
    have hb : b ≠ 0 := by
      intro hz
      have hdiv : A.equationPolynomial H ∣ (1 : CoordinateRing (d := d)) := by
        rw [← hrel, hz, zero_smul, add_zero, MvPolynomial.smul_eq_C_mul]
        exact dvd_mul_left _ _
      exact (A.equationPolynomial_irreducible H).not_isUnit (isUnit_of_dvd_one hdiv)
    have hs : b • A.equationPolynomial K =
        (1 : CoordinateRing (d := d)) - a • A.equationPolynomial H := by
      rw [← hrel]
      abel
    have hK : A.equationPolynomial K = b⁻¹ • (1 : CoordinateRing (d := d)) -
        (b⁻¹ * a) • A.equationPolynomial H := by
      calc
        A.equationPolynomial K = b⁻¹ • (b • A.equationPolynomial K) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • ((1 : CoordinateRing (d := d)) - a • A.equationPolynomial H) :=
          congrArg (fun p : CoordinateRing (d := d) ↦ b⁻¹ • p) hs
        _ = _ := by rw [smul_sub, smul_smul]
    have hpoly : A.equationPolynomial K =
        MvPolynomial.C (-(b⁻¹ * a)) * A.equationPolynomial H + MvPolynomial.C b⁻¹ := by
      simpa only [MvPolynomial.smul_eq_C_mul, mul_one, sub_eq_add_neg,
        map_neg, neg_mul, add_comm] using hK
    exact ⟨-(b⁻¹ * a), A.normal_relation_of_equationPolynomial_affine_relation
      H K (-(b⁻¹ * a)) b⁻¹ hpoly⟩
  · rintro ⟨c, hc⟩
    let δ := c * A.offset H - A.offset K
    have hδ : δ ≠ 0 := A.parallel_offset_discrepancy_ne_zero H K hHK c hc
    have hpoly := A.equationPolynomial_affine_relation_of_parallel H K c hc
    have hconst : A.equationPolynomial K - c • A.equationPolynomial H = MvPolynomial.C δ := by
      rw [hpoly, MvPolynomial.smul_eq_C_mul]
      abel
    have heq : (1 : CoordinateRing (d := d)) =
        δ⁻¹ • (A.equationPolynomial K - c • A.equationPolynomial H) := by
      rw [hconst, MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_mul,
        inv_mul_cancel₀ hδ, map_one]
    rw [heq]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact Submodule.subset_span (by simp)
    · apply Submodule.smul_mem
      exact Submodule.subset_span (by simp)

/-- The actual equation-span family of distinct original coordinate pairs. -/
def ActualEquationPairSpanFamily :=
  {X : Submodule ℂ (CoordinateRing (d := d)) //
    ∃ H K : ι, H ≠ K ∧ X = A.affineEquationPairSpan H K}

/-- Finiteness is derived from the actual finite distinct-pair index set. -/
instance actualEquationPairSpanFamily_finite : Finite A.ActualEquationPairSpanFamily := by
  let f : {p : ι × ι // p.1 ≠ p.2} → A.ActualEquationPairSpanFamily :=
    fun p ↦ ⟨A.affineEquationPairSpan p.val.1 p.val.2, p.val.1, p.val.2, p.property, rfl⟩
  apply Finite.of_surjective f
  rintro ⟨X, H, K, hHK, hX⟩
  refine ⟨⟨(H, K), hHK⟩, ?_⟩
  apply Subtype.ext
  exact hX.symm

end ChenRanks.AffineArrangement
