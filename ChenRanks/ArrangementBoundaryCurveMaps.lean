import ChenRanks.TwicePuncturedComplexMaps
import ChenRanks.ArrangementParallelRelations

/-!
# Actual twice-punctured-plane maps for original affine quadratic boundaries

The original affine offsets enter the parallel-pair map through their
actual nonzero discrepancy. For an actual three-equation relation, the
actual ratio is defined on the original complement and avoids both 0
and 1. The two actual nonzero functions on the target pull back to actual
constant multiples of the original equation ratios.

These are actual continuous-map identities, before any singular
Steinberg cup relation is proved. No expected cup vanishing is an input.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance arrangementBoundaryCurveMapsDecidableEq : DecidableEq ι := Classical.decEq ι

/-- A scalar relating actual nonzero normals is itself nonzero. -/
theorem parallel_normal_scalar_ne_zero (H K : ι) (c : ℂ)
    (hc : A.normal K = c • A.normal H) : c ≠ 0 := by
  intro hz
  apply A.normal_ne_zero K
  rw [hc, hz, zero_smul]

/-- The actual equation functions on the original complement retain
the original affine discrepancy of a parallel pair. -/
theorem equationComplementNonzeroComplexMap_parallel_relation
    (H K : ι) (c : ℂ) (hc : A.normal K = c • A.normal H) (x : A.Complement) :
    (A.equationComplementNonzeroComplexMap K x : ℂ) =
      c * (A.equationComplementNonzeroComplexMap H x : ℂ) +
        (c * A.offset H - A.offset K) := by
  change A.normal K x.val - A.offset K =
    c * (A.normal H x.val - A.offset H) + (c * A.offset H - A.offset K)
  rw [hc]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The actual parallel-pair ratio maps the original complement to the
actual twice-punctured plane. Distinctness supplies the nonzero offset
discrepancy; neither puncture avoidance is assumed. -/
def parallelBoundaryCurveMap (H K : ι) (hHK : H ≠ K) (c : ℂ)
    (hc : A.normal K = c • A.normal H) : C(A.Complement, TwicePuncturedComplex) where
  toFun x := by
    let δ := c * A.offset H - A.offset K
    have hδ : δ ≠ 0 := A.parallel_offset_discrepancy_ne_zero H K hHK c hc
    have hc0 : c ≠ 0 := A.parallel_normal_scalar_ne_zero H K c hc
    refine ⟨(-c * (A.equationComplementNonzeroComplexMap H x : ℂ)) / δ, ?_, ?_⟩
    · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc0)
        (A.equationComplementNonzeroComplexMap H x).property) hδ
    · intro ht
      have hnum := (div_eq_one_iff_eq hδ).mp ht
      apply (A.equationComplementNonzeroComplexMap K x).property
      rw [A.equationComplementNonzeroComplexMap_parallel_relation H K c hc x]
      change c * (A.equationComplementNonzeroComplexMap H x : ℂ) + δ = 0
      linear_combination -hnum
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_subtype_val.comp
      (A.equationComplementNonzeroComplexMap H).continuous)).div_const _

@[simp] theorem parallelBoundaryCurveMap_coe (H K : ι) (hHK : H ≠ K)
    (c : ℂ) (hc : A.normal K = c • A.normal H) (x : A.Complement) :
    (A.parallelBoundaryCurveMap H K hHK c hc x : ℂ) =
      (-c * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
        (c * A.offset H - A.offset K) := rfl

/-- Pullback of z is the actual constant multiple of the original first
equation, as an equality of actual nonzero continuous maps. -/
theorem parallelBoundaryCurveMap_zero_factor (H K : ι) (hHK : H ≠ K)
    (c : ℂ) (hc : A.normal K = c • A.normal H) :
    twicePuncturedComplexZeroMap.comp (A.parallelBoundaryCurveMap H K hHK c hc) =
      nonzeroComplexMapScale (-c / (c * A.offset H - A.offset K))
        (div_ne_zero (neg_ne_zero.mpr (A.parallel_normal_scalar_ne_zero H K c hc))
          (A.parallel_offset_discrepancy_ne_zero H K hHK c hc))
        (A.equationComplementNonzeroComplexMap H) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (-c * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
      (c * A.offset H - A.offset K) =
    (-c / (c * A.offset H - A.offset K)) *
      (A.equationComplementNonzeroComplexMap H x : ℂ)
  simp only [div_eq_mul_inv]
  ring

/-- Pullback of 1-z is the actual second original equation divided by
the actual nonzero affine discrepancy. -/
theorem parallelBoundaryCurveMap_one_factor (H K : ι) (hHK : H ≠ K)
    (c : ℂ) (hc : A.normal K = c • A.normal H) :
    twicePuncturedComplexOneMap.comp (A.parallelBoundaryCurveMap H K hHK c hc) =
      nonzeroComplexMapScale (c * A.offset H - A.offset K)⁻¹
        (inv_ne_zero (A.parallel_offset_discrepancy_ne_zero H K hHK c hc))
        (A.equationComplementNonzeroComplexMap K) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change 1 - (-c * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
      (c * A.offset H - A.offset K) =
    (c * A.offset H - A.offset K)⁻¹ *
      (A.equationComplementNonzeroComplexMap K x : ℂ)
  rw [A.equationComplementNonzeroComplexMap_parallel_relation H K c hc x]
  field_simp [A.parallel_offset_discrepancy_ne_zero H K hHK c hc]
  ring

/-- The original polynomial relation evaluates to the actual original
nonzero functions, with the same constants and affine offsets. -/
theorem equationComplementNonzeroComplexMap_triple_relation
    (H K L : ι) (a b : ℂ)
    (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) (x : A.Complement) :
    (A.equationComplementNonzeroComplexMap L x : ℂ) =
      a * (A.equationComplementNonzeroComplexMap H x : ℂ) +
        b * (A.equationComplementNonzeroComplexMap K x : ℂ) := by
  rw [A.equationComplementNonzeroComplexMap_eq_polynomial_eval,
    A.equationComplementNonzeroComplexMap_eq_polynomial_eval,
    A.equationComplementNonzeroComplexMap_eq_polynomial_eval, h]
  simp [Algebra.smul_def]

/-- In a genuine triple of distinct original hyperplanes the first
coefficient cannot vanish. This follows from actual nondivisibility. -/
theorem triple_equation_first_coefficient_ne_zero (H K L : ι) (hKL : K ≠ L)
    (a b : ℂ) (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) : a ≠ 0 := by
  intro ha
  apply A.equationPolynomial_not_dvd_of_ne K L hKL
  refine ⟨MvPolynomial.C b, ?_⟩
  rw [h, ha, zero_smul, zero_add, MvPolynomial.smul_eq_C_mul]
  change MvPolynomial.C b * A.equationPolynomial K =
    A.equationPolynomial K * MvPolynomial.C b
  exact mul_comm _ _

/-- The same actual argument proves the second coefficient nonzero. -/
theorem triple_equation_second_coefficient_ne_zero (H K L : ι) (hHL : H ≠ L)
    (a b : ℂ) (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) : b ≠ 0 := by
  intro hb
  apply A.equationPolynomial_not_dvd_of_ne H L hHL
  refine ⟨MvPolynomial.C a, ?_⟩
  rw [h, hb, zero_smul, add_zero, MvPolynomial.smul_eq_C_mul]
  change MvPolynomial.C a * A.equationPolynomial H =
    A.equationPolynomial H * MvPolynomial.C a
  exact mul_comm _ _

/-- The actual triple ratio is a genuine map on the original complement
to the actual twice-punctured plane. -/
def tripleBoundaryCurveMap (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L)
    (a b : ℂ) (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    C(A.Complement, TwicePuncturedComplex) where
  toFun x := by
    have ha := A.triple_equation_first_coefficient_ne_zero H K L hKL a b h
    have hb := A.triple_equation_second_coefficient_ne_zero H K L hHL a b h
    have hden : b * (A.equationComplementNonzeroComplexMap K x : ℂ) ≠ 0 :=
      mul_ne_zero hb (A.equationComplementNonzeroComplexMap K x).property
    refine ⟨(-a * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
      (b * (A.equationComplementNonzeroComplexMap K x : ℂ)), ?_, ?_⟩
    · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha)
        (A.equationComplementNonzeroComplexMap H x).property) hden
    · intro ht
      have hnum := (div_eq_one_iff_eq hden).mp ht
      apply (A.equationComplementNonzeroComplexMap L x).property
      rw [A.equationComplementNonzeroComplexMap_triple_relation H K L a b h x]
      linear_combination -hnum
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact continuous_const.mul (continuous_subtype_val.comp
        (A.equationComplementNonzeroComplexMap H).continuous)
    · exact continuous_const.mul (continuous_subtype_val.comp
        (A.equationComplementNonzeroComplexMap K).continuous)
    · intro x
      exact mul_ne_zero (A.triple_equation_second_coefficient_ne_zero H K L hHL a b h)
        (A.equationComplementNonzeroComplexMap K x).property

@[simp] theorem tripleBoundaryCurveMap_coe (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L)
    (a b : ℂ) (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) (x : A.Complement) :
    (A.tripleBoundaryCurveMap H K L hHL hKL a b h x : ℂ) =
      (-a * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
        (b * (A.equationComplementNonzeroComplexMap K x : ℂ)) := rfl

/-- Pullback of z is the actual constant multiple of the actual ratio
of the first two original equations. -/
theorem tripleBoundaryCurveMap_zero_factor (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L)
    (a b : ℂ) (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    twicePuncturedComplexZeroMap.comp (A.tripleBoundaryCurveMap H K L hHL hKL a b h) =
      nonzeroComplexMapScale (-a / b)
        (div_ne_zero (neg_ne_zero.mpr
          (A.triple_equation_first_coefficient_ne_zero H K L hKL a b h))
          (A.triple_equation_second_coefficient_ne_zero H K L hHL a b h))
        (nonzeroComplexMapQuotient (A.equationComplementNonzeroComplexMap H)
          (A.equationComplementNonzeroComplexMap K)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (-a * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
      (b * (A.equationComplementNonzeroComplexMap K x : ℂ)) =
    (-a / b) * ((A.equationComplementNonzeroComplexMap H x : ℂ) /
      (A.equationComplementNonzeroComplexMap K x : ℂ))
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Pullback of 1-z is the actual constant multiple of the actual ratio
of the third and second original equations. -/
theorem tripleBoundaryCurveMap_one_factor (H K L : ι) (hHL : H ≠ L) (hKL : K ≠ L)
    (a b : ℂ) (h : A.equationPolynomial L =
      a • A.equationPolynomial H + b • A.equationPolynomial K) :
    twicePuncturedComplexOneMap.comp (A.tripleBoundaryCurveMap H K L hHL hKL a b h) =
      nonzeroComplexMapScale b⁻¹
        (inv_ne_zero (A.triple_equation_second_coefficient_ne_zero H K L hHL a b h))
        (nonzeroComplexMapQuotient (A.equationComplementNonzeroComplexMap L)
          (A.equationComplementNonzeroComplexMap K)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change 1 - (-a * (A.equationComplementNonzeroComplexMap H x : ℂ)) /
      (b * (A.equationComplementNonzeroComplexMap K x : ℂ)) =
    b⁻¹ * ((A.equationComplementNonzeroComplexMap L x : ℂ) /
      (A.equationComplementNonzeroComplexMap K x : ℂ))
  rw [A.equationComplementNonzeroComplexMap_triple_relation H K L a b h x]
  field_simp [A.triple_equation_second_coefficient_ne_zero H K L hHL a b h,
    (A.equationComplementNonzeroComplexMap K x).property]
  ring

/-- Repeated original indices give the actual zero boundary, without
constructing a ratio with a zero coefficient. -/
theorem tripleBoundary_eq_zero_of_repeated (H K L : ι)
    (h : H = K ∨ H = L ∨ K = L) : tripleBoundary H K L = 0 := by
  rcases h with h | h | h
  · subst K
    simp only [tripleBoundary, sub_self, wedge_self, zero_add]
  · subst L
    simp only [tripleBoundary, wedge_self, sub_zero]
    rw [wedge_swap (k := ℂ) (E := ι → ℂ)
      (Pi.single K (1 : ℂ) : ι → ℂ) (Pi.single H (1 : ℂ) : ι → ℂ)]
    exact neg_add_cancel _
  · subst L
    simp only [tripleBoundary, wedge_self, zero_sub, neg_add_cancel]

end ChenRanks.AffineArrangement
