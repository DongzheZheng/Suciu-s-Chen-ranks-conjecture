import ChenRanks.ProperConstancy
import ChenRanks.AlgebraicDifferentials
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Proper regular functions over an arbitrary base field

This is the generic-fibre version of the paper's proper-fibre mechanism.
Actual regular sections of a proper integral scheme are algebraic over
its base field. The conclusion is in the actual scheme function field,
with the scalar algebra constructed from the actual structure morphism
and actual generic-point germ. Algebraic closedness of the base field is
not needed for algebraicity or relative differential vanishing.

The manuscript's actual generic fibre and the comparison of its function
field with the ambient variety's function field remain to be constructed.
Neither comparison is assumed in these definitions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ChenRanks

universe u

variable {k : Type u} [Field k]

/-- The actual generic-point germ on the top open; nonemptiness is proved
explicitly from the actual generic point. -/
abbrev topFunctionFieldGerm (X : Scheme) [IsIntegral X] :
    Γ(X, ⊤) ⟶ X.functionField :=
  @Scheme.germToFunctionField X inferInstance (⊤ : X.Opens)
    ⟨⟨genericPoint X, by simp⟩⟩

/-- The integral map on actual global functions supplied by properness. -/
theorem globalScalarMap_isIntegral {X : Scheme} (f : X ⟶ Spec (.of k))
    [UniversallyClosed f] : (globalScalarMap f).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- Actual scalars in the actual generic-point function field. -/
abbrev structureFunctionFieldAlgebra {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) : Algebra k X.functionField :=
  ((topFunctionFieldGerm X).hom.comp (globalScalarMap f)).toAlgebra

/-- A true global regular section is integral in the actual function field,
for the scalar algebra induced by the actual structure morphism. -/
theorem global_regular_function_germ_isIntegral
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [UniversallyClosed f] (s : Γ(X, ⊤)) :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra f
    _root_.IsIntegral k (topFunctionFieldGerm X s) := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra f
  exact (globalScalarMap_isIntegral f s).map (topFunctionFieldGerm X).hom

/-- The actual rational germ of a global proper regular function is algebraic
without an algebraically closed base-field hypothesis. -/
theorem global_regular_function_germ_isAlgebraic
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [UniversallyClosed f] (s : Γ(X, ⊤)) :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra f
    IsAlgebraic k (topFunctionFieldGerm X s) := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra f
  exact (global_regular_function_germ_isIntegral f s).isAlgebraic

/-- Characteristic-zero relative differential vanishing for the same actual
rational germ. This is not a statement about global differential sheaf sections. -/
theorem global_regular_function_germ_relative_differential_eq_zero [CharZero k]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [UniversallyClosed f] (s : Γ(X, ⊤)) :
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra f
    KaehlerDifferential.D k X.functionField (topFunctionFieldGerm X s) = 0 := by
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra f
  exact relative_differential_eq_zero_of_isAlgebraic
    (topFunctionFieldGerm X s) (global_regular_function_germ_isAlgebraic f s)

end ChenRanks
