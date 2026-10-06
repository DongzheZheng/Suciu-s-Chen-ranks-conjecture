import ChenRanks.ArrangementEquationPhaseMaps
import ChenRanks.CircleLoopContractionWinding

/-!
# Actual winding around a point outside a genuine path bound

The integer is obtained by applying the original phase map to the actual
translated path. A point beyond the actual norm bound has zero winding,
by the explicitly constructed straight contraction. This is a geometric
ingredient for proving finite support of puncture winding sums.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The original translated nonvanishing path, with its genuine subspace topology. -/
def translatedNonzeroComplexPath (γ : C(I, ℂ)) (z : ℂ)
    (havoid : ∀ t, γ t ≠ z) : C(I, NonzeroComplex) where
  toFun t := ⟨γ t - z, sub_ne_zero.mpr (havoid t)⟩
  continuous_toFun := Continuous.subtype_mk (γ.continuous.sub continuous_const) _

/-- The actual covering-space integer of the original translated phase path. -/
def complexPathWindingAround (γ : C(I, ℂ)) (z : ℂ)
    (havoid : ∀ t, γ t ≠ z) : ℤ :=
  circlePathIntegerIncrement
    (nonzeroComplexCircleMap.comp (translatedNonzeroComplexPath γ z havoid))

private theorem boundedComplexPath_smul_ne (γ : C(I, ℂ)) (z : ℂ)
    (hbound : ∀ t, ‖γ t‖ < ‖z‖) (p : I × I) :
    (((p.1 : ℝ) : ℂ) * γ p.2) ≠ z := by
  intro heq
  have hn := congrArg norm heq
  rw [norm_mul, Complex.norm_of_nonneg p.1.property.1] at hn
  have hb := hbound p.2
  have ht := p.1.property.2
  have hc := norm_nonneg (γ p.2)
  nlinarith

/-- The real straight contraction is nonzero after translation at every actual point. -/
def boundedComplexPathTranslatedContraction (γ : C(I, ℂ)) (z : ℂ)
    (hbound : ∀ t, ‖γ t‖ < ‖z‖) : C(I × I, NonzeroComplex) where
  toFun p := ⟨((p.1 : ℝ) : ℂ) * γ p.2 - z,
    sub_ne_zero.mpr (boundedComplexPath_smul_ne γ z hbound p)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)).mul
      (γ.continuous.comp continuous_snd)).sub continuous_const

/-- Every original closed path has actual winding zero about a point beyond its norm bound. -/
theorem complexPathWindingAround_eq_zero_of_norm_bound (γ : C(I, ℂ))
    (hγ : γ 0 = γ 1) (z : ℂ) (havoid : ∀ t, γ t ≠ z)
    (hbound : ∀ t, ‖γ t‖ < ‖z‖) :
    complexPathWindingAround γ z havoid = 0 := by
  have hz : z ≠ 0 := by
    intro hz
    have hb := hbound 0
    rw [hz, norm_zero] at hb
    exact (not_lt_of_ge (norm_nonneg (γ 0))) hb
  let F := nonzeroComplexCircleMap.comp
    (boundedComplexPathTranslatedContraction γ z hbound)
  let a := nonzeroComplexCircleMap (⟨-z, neg_ne_zero.mpr hz⟩ : NonzeroComplex)
  apply circlePathIntegerIncrement_eq_zero_of_loop_contraction
    (nonzeroComplexCircleMap.comp (translatedNonzeroComplexPath γ z havoid)) F a
  · intro t
    apply congrArg nonzeroComplexCircleMap
    apply Subtype.ext
    change (((0 : I) : ℝ) : ℂ) * γ t - z = -z
    simp
  · intro t
    apply congrArg nonzeroComplexCircleMap
    apply Subtype.ext
    change (((1 : I) : ℝ) : ℂ) * γ t - z = γ t - z
    simp
  · intro s
    apply congrArg nonzeroComplexCircleMap
    apply Subtype.ext
    change ((s : ℝ) : ℂ) * γ 0 - z = ((s : ℝ) : ℂ) * γ 1 - z
    rw [hγ]

end ChenRanks
