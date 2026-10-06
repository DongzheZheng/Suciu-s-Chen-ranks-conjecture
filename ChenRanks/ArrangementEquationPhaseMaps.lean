import ChenRanks.ArrangementDifferentials
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Uncompiled preparation outside the active Lean sources.

The maps are induced by the actual nonvanishing original equations on
the actual complement. Taking argument in the quotient angle removes
the discontinuity of a chosen real argument. No winding class, H¹ basis,
Orlik–Solomon comparison, or Chen comparison is assumed or asserted. -/

noncomputable section

namespace ChenRanks

/-- The punctured plane with its actual subspace topology. -/
abbrev NonzeroComplex := {z : ℂ // z ≠ 0}

/-- The argument of an actual nonzero complex number, in the actual
quotient circle, is continuous even across a chosen branch cut. -/
def nonzeroComplexAngleMap : C(NonzeroComplex, Real.Angle) where
  toFun z := (Complex.arg (z : ℂ) : Real.Angle)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (Complex.continuousAt_arg_coe_angle z.property).comp
      continuousAt_subtype_val

/-- The same actual phase as a point of the actual unit circle. -/
def nonzeroComplexCircleMap : C(NonzeroComplex, Circle) :=
  (⟨AddCircle.homeomorphCircle', AddCircle.homeomorphCircle'.continuous⟩ :
    C(Real.Angle, Circle)).comp nonzeroComplexAngleMap

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- The actual original equation defines a continuous map from the
actual complement into the actual punctured plane. -/
def equationComplementNonzeroComplexMap (H : ι) :
    C(A.Complement, NonzeroComplex) where
  toFun x := ⟨A.normal H x.val - A.offset H, sub_ne_zero.mpr (x.property H)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((A.normal H).continuous_of_finiteDimensional.comp
      continuous_subtype_val).sub continuous_const

/-- This is the original polynomial equation evaluated at the same
actual complement point, rather than an assigned topological label. -/
theorem equationComplementNonzeroComplexMap_eq_polynomial_eval
    (H : ι) (x : A.Complement) :
    (A.equationComplementNonzeroComplexMap H x : ℂ) =
      MvPolynomial.eval x.val (A.equationPolynomial H) :=
  (A.equationPolynomial_eval H x.val).symm

/-- The actual equation's continuous quotient-angle map. -/
def equationComplementAngleMap (H : ι) : C(A.Complement, Real.Angle) :=
  nonzeroComplexAngleMap.comp (A.equationComplementNonzeroComplexMap H)

/-- The actual equation's continuous unit-circle map. Pullback of a
genuine integer winding cocycle along this map will define its actual
singular degree-one class. That cocycle is not defined by this file. -/
def equationComplementCircleMap (H : ι) : C(A.Complement, Circle) :=
  nonzeroComplexCircleMap.comp (A.equationComplementNonzeroComplexMap H)

end AffineArrangement

end ChenRanks
