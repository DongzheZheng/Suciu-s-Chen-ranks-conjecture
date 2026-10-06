import ChenRanks.NonzeroComplexPhaseMultiplication
import ChenRanks.TwicePuncturedComplexMaps
import ChenRanks.SingularCircleProductClasses

/-!
# Original nonzero-function winding classes under scaling and division

All maps retain their original complex-valued functions and subspace
topologies. The class identities follow from genuine phase identities
and the explicit principal-argument carry primitive on native cochains.
No logarithmic or cohomological model comparison is an input.
-/

noncomputable section

namespace ChenRanks

/-- The phase of the original inverse nonzero number is the inverse phase. -/
theorem nonzeroComplexCircleMap_inv (z : NonzeroComplex) :
    nonzeroComplexCircleMap (⟨(z : ℂ)⁻¹, inv_ne_zero z.property⟩ : NonzeroComplex) =
      (nonzeroComplexCircleMap z)⁻¹ := by
  let w : NonzeroComplex := ⟨(z : ℂ)⁻¹, inv_ne_zero z.property⟩
  have hprod := nonzeroComplexCircleMap_mul z w
  have hw : (⟨(z : ℂ) * (w : ℂ), mul_ne_zero z.property w.property⟩ : NonzeroComplex) =
      ⟨1, one_ne_zero⟩ := by
    apply Subtype.ext
    exact mul_inv_cancel₀ z.property
  rw [hw] at hprod
  have hone : nonzeroComplexCircleMap (⟨1, one_ne_zero⟩ : NonzeroComplex) = 1 :=
    nonzeroComplexCircleMap_circle 1
  rw [hone] at hprod
  change nonzeroComplexCircleMap w = _
  calc
    nonzeroComplexCircleMap w =
        (nonzeroComplexCircleMap z)⁻¹ *
          (nonzeroComplexCircleMap z * nonzeroComplexCircleMap w) := by simp
    _ = (nonzeroComplexCircleMap z)⁻¹ := by rw [← hprod, mul_one]

variable {X : Type} [TopologicalSpace X]

theorem nonzeroComplexCircleMap_scale_comp (c : ℂ) (hc : c ≠ 0)
    (f : C(X, NonzeroComplex)) :
    nonzeroComplexCircleMap.comp (nonzeroComplexMapScale c hc f) =
      (ContinuousMap.const X (nonzeroComplexCircleMap ⟨c, hc⟩)) *
        (nonzeroComplexCircleMap.comp f) := by
  apply ContinuousMap.ext
  intro x
  exact nonzeroComplexCircleMap_mul (⟨c, hc⟩ : NonzeroComplex) (f x)

theorem nonzeroComplexCircleMap_quotient_comp (f g : C(X, NonzeroComplex)) :
    nonzeroComplexCircleMap.comp (nonzeroComplexMapQuotient f g) =
      (nonzeroComplexCircleMap.comp f) * (nonzeroComplexCircleMap.comp g)⁻¹ := by
  apply ContinuousMap.ext
  intro x
  have h := nonzeroComplexCircleMap_mul (f x)
    (⟨(g x : ℂ)⁻¹, inv_ne_zero (g x).property⟩ : NonzeroComplex)
  rw [nonzeroComplexCircleMap_inv] at h
  change nonzeroComplexCircleMap
      (⟨(f x : ℂ) / (g x : ℂ), div_ne_zero (f x).property (g x).property⟩ :
        NonzeroComplex) =
    nonzeroComplexCircleMap (f x) * (nonzeroComplexCircleMap (g x))⁻¹
  simpa only [div_eq_mul_inv] using h

open SingularCohomology

variable (k : Type) [Field k]

/-- Actual constant scaling does not change the native winding class. -/
theorem cohomologyPullback_nonzero_winding_scale (c : ℂ) (hc : c ≠ 0)
    (f : C(X, NonzeroComplex)) :
    cohomologyPullback k
        (nonzeroComplexCircleMap.comp (nonzeroComplexMapScale c hc f)) 1
        (circleWindingClass k) =
      cohomologyPullback k (nonzeroComplexCircleMap.comp f) 1 (circleWindingClass k) := by
  rw [nonzeroComplexCircleMap_scale_comp, cohomologyPullback_circleWindingClass_mul,
    cohomologyPullback_circleWindingClass_const, zero_add]

/-- The actual quotient function has the difference of the two native winding classes. -/
theorem cohomologyPullback_nonzero_winding_quotient (f g : C(X, NonzeroComplex)) :
    cohomologyPullback k (nonzeroComplexCircleMap.comp (nonzeroComplexMapQuotient f g))
        1 (circleWindingClass k) =
      cohomologyPullback k (nonzeroComplexCircleMap.comp f) 1 (circleWindingClass k) -
        cohomologyPullback k (nonzeroComplexCircleMap.comp g) 1 (circleWindingClass k) := by
  rw [nonzeroComplexCircleMap_quotient_comp, cohomologyPullback_circleWindingClass_mul,
    cohomologyPullback_circleWindingClass_inv, sub_eq_add_neg]

end ChenRanks
