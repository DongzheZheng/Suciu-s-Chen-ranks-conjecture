import ChenRanks.ArrangementEquationPhaseMaps

/-!
# The actual twice-punctured complex plane and its two actual phase maps

The space is the original subspace of ℂ with 0 and 1 removed. Both
nonvanishing functions and both phase maps are actual continuous maps.
No cohomology vanishing or cup-product relation is asserted here.
-/

noncomputable section

namespace ChenRanks

/-- The actual complex plane with precisely 0 and 1 removed. -/
abbrev TwicePuncturedComplex := {z : ℂ // z ≠ 0 ∧ z ≠ 1}

/-- The actual nonzero function z on the actual twice-punctured plane. -/
def twicePuncturedComplexZeroMap : C(TwicePuncturedComplex, NonzeroComplex) where
  toFun z := ⟨z.val, z.property.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The actual nonzero function 1-z on the same actual plane. -/
def twicePuncturedComplexOneMap : C(TwicePuncturedComplex, NonzeroComplex) where
  toFun z := ⟨1 - z.val, sub_ne_zero.mpr z.property.2.symm⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- The genuine continuous phase of z. -/
def twicePuncturedComplexZeroPhase : C(TwicePuncturedComplex, Circle) :=
  nonzeroComplexCircleMap.comp twicePuncturedComplexZeroMap

/-- The genuine continuous phase of 1-z. -/
def twicePuncturedComplexOnePhase : C(TwicePuncturedComplex, Circle) :=
  nonzeroComplexCircleMap.comp twicePuncturedComplexOneMap

@[simp] theorem twicePuncturedComplexZeroMap_coe (z : TwicePuncturedComplex) :
    (twicePuncturedComplexZeroMap z : ℂ) = z.val := rfl

@[simp] theorem twicePuncturedComplexOneMap_coe (z : TwicePuncturedComplex) :
    (twicePuncturedComplexOneMap z : ℂ) = 1 - z.val := rfl

section ActualNonzeroMapOperations

variable {X : Type*} [TopologicalSpace X]

/-- Actual multiplication by an actual nonzero constant, retaining the
original subspace topology and the original complex-valued function. -/
def nonzeroComplexMapScale (c : ℂ) (hc : c ≠ 0) (f : C(X, NonzeroComplex)) :
    C(X, NonzeroComplex) where
  toFun x := ⟨c * (f x : ℂ), mul_ne_zero hc (f x).property⟩
  continuous_toFun :=
    (continuous_const.mul (continuous_subtype_val.comp f.continuous)).subtype_mk _

/-- The actual quotient of two actual nonvanishing continuous functions. -/
def nonzeroComplexMapQuotient (f g : C(X, NonzeroComplex)) :
    C(X, NonzeroComplex) where
  toFun x := ⟨(f x : ℂ) / (g x : ℂ), div_ne_zero (f x).property (g x).property⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp f.continuous).div
      (continuous_subtype_val.comp g.continuous) (fun x => (g x).property)).subtype_mk _

@[simp] theorem nonzeroComplexMapScale_coe (c : ℂ) (hc : c ≠ 0)
    (f : C(X, NonzeroComplex)) (x : X) :
    (nonzeroComplexMapScale c hc f x : ℂ) = c * (f x : ℂ) := rfl

@[simp] theorem nonzeroComplexMapQuotient_coe
    (f g : C(X, NonzeroComplex)) (x : X) :
    (nonzeroComplexMapQuotient f g x : ℂ) = (f x : ℂ) / (g x : ℂ) := rfl

end ActualNonzeroMapOperations

end ChenRanks
