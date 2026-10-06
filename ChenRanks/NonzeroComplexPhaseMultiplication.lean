import ChenRanks.ArrangementEquationPhaseMaps

/-! Multiplication of the genuine continuous phase of original nonzero numbers. -/

noncomputable section
namespace ChenRanks

/-- The actual quotient-angle phase is multiplicative on actual nonzero numbers. -/
theorem nonzeroComplexCircleMap_mul (z w : NonzeroComplex) :
    nonzeroComplexCircleMap ⟨(z : ℂ) * (w : ℂ), mul_ne_zero z.property w.property⟩ =
      nonzeroComplexCircleMap z * nonzeroComplexCircleMap w := by
  change Real.Angle.toCircle (Complex.arg ((z : ℂ) * (w : ℂ)) : Real.Angle) =
    Real.Angle.toCircle (Complex.arg (z : ℂ) : Real.Angle) *
      Real.Angle.toCircle (Complex.arg (w : ℂ) : Real.Angle)
  rw [Complex.arg_mul_coe_angle z.property w.property, Real.Angle.toCircle_add]

/-- A genuine unit-circle factor is itself the actual nonzero-complex phase. -/
theorem nonzeroComplexCircleMap_circle (u : Circle) :
    nonzeroComplexCircleMap ⟨(u : ℂ), u.coe_ne_zero⟩ = u :=
  Circle.exp_arg u

end ChenRanks
