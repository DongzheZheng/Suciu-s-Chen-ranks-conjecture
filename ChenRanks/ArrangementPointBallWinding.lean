import ChenRanks.ArrangementPointAvoidanceNeighborhood
import ChenRanks.ArrangementEquationPhaseMaps
import ChenRanks.CircleLoopContractionWinding

/-!
# True winding zero for actual nonincident equations inside the original ball

The contraction is the actual straight-line homotopy in the original
affine vector space. The original finite avoidance radius proves that
its selected original equation is nonzero throughout. The true covering
homotopy theorem then computes the actual integer; no integer value,
contraction, or lift is assumed.
-/

noncomputable section
open unitInterval
namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The original ball contains the true straight contraction of every path point. -/
theorem pointBall_straightContraction_dist_lt (x : Fin d → ℂ)
    (γ : C(I, A.Complement))
    (hball : ∀ s, dist (γ s).val x < A.actualPointAvoidanceRadius x) (p : I × I) :
    dist (x + (((p.1 : ℝ) : ℂ) • ((γ p.2).val - x))) x <
      A.actualPointAvoidanceRadius x := by
  rw [dist_eq_norm]
  simp only [add_sub_cancel_left]
  rw [norm_smul, Complex.norm_of_nonneg p.1.property.1]
  have hb := hball p.2
  rw [dist_eq_norm] at hb
  have hmul : (p.1 : ℝ) * ‖(γ p.2).val - x‖ ≤ ‖(γ p.2).val - x‖ := by
    nlinarith [norm_nonneg ((γ p.2).val - x), p.1.property.2]
  exact lt_of_le_of_lt hmul hb

/-- The true straight contraction of one actual nonincident equation is nonvanishing. -/
def pointBallEquationContractionNonzeroMap (x : Fin d → ℂ) (K : ι)
    (hKx : A.normal K x ≠ A.offset K) (γ : C(I, A.Complement))
    (hball : ∀ s, dist (γ s).val x < A.actualPointAvoidanceRadius x) :
    C(I × I, NonzeroComplex) where
  toFun p := ⟨A.normal K (x + (((p.1 : ℝ) : ℂ) • ((γ p.2).val - x))) - A.offset K,
    sub_ne_zero.mpr (A.actualPointAvoidanceRadius_avoids x _
      (A.pointBall_straightContraction_dist_lt x γ hball p) K hKx)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : I × I =>
        x + (((p.1 : ℝ) : ℂ) • ((γ p.2).val - x))) := by
      exact continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).smul
          ((continuous_subtype_val.comp (γ.continuous.comp continuous_snd)).sub continuous_const))
    exact ((A.normal K).continuous_of_finiteDimensional.comp hc).sub continuous_const

/-- The original loop's true nonincident equation integer is zero in the actual avoidance ball. -/
theorem pointBall_equation_increment_zero (x : Fin d → ℂ) (K : ι)
    (hKx : A.normal K x ≠ A.offset K) (γ : C(I, A.Complement)) (hγ : γ 0 = γ 1)
    (hball : ∀ s, dist (γ s).val x < A.actualPointAvoidanceRadius x) :
    circlePathIntegerIncrement ((A.equationComplementCircleMap K).comp γ) = 0 := by
  let F := nonzeroComplexCircleMap.comp
    (A.pointBallEquationContractionNonzeroMap x K hKx γ hball)
  let z := nonzeroComplexCircleMap
    ⟨A.normal K x - A.offset K, sub_ne_zero.mpr hKx⟩
  apply circlePathIntegerIncrement_eq_zero_of_loop_contraction
    ((A.equationComplementCircleMap K).comp γ) F z
  · intro s
    apply congrArg nonzeroComplexCircleMap
    apply Subtype.ext
    change A.normal K (x + ((((0 : I) : ℝ) : ℂ) • ((γ s).val - x))) - A.offset K = _
    simp
  · intro s
    apply congrArg nonzeroComplexCircleMap
    apply Subtype.ext
    change A.normal K (x + ((((1 : I) : ℝ) : ℂ) • ((γ s).val - x))) - A.offset K =
      A.normal K (γ s).val - A.offset K
    change A.normal K (x + (1 : ℂ) • ((γ s).val - x)) - A.offset K =
      A.normal K (γ s).val - A.offset K
    simp only [one_smul]
    congr 2
    abel
  · intro t
    apply congrArg nonzeroComplexCircleMap
    apply Subtype.ext
    change A.normal K (x + (((t : ℝ) : ℂ) • ((γ 0).val - x))) - A.offset K =
      A.normal K (x + (((t : ℝ) : ℂ) • ((γ 1).val - x))) - A.offset K
    rw [hγ]

end ChenRanks.AffineArrangement
