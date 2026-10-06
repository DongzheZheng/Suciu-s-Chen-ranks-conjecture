import ChenRanks.FiniteTypeNormalization
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Original structural scalar actions on actual affine charts

These maps are built from the actual structural morphism, its actual
restriction to a chart, and the native spectrum section comparison.
The finite-type hypothesis is inherited by actual affine section rings.
This makes characteristic-zero normalization applicable to actual chart
rings without an additional ring-finiteness assumption.
-/

noncomputable section

namespace ChenRanks

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual structural map on the original open's section ring. -/
def chartScalarMap (σ : X ⟶ Spec (.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  (σ.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The chart's coefficient action comes from the actual structural map. -/
abbrev chartScalarAlgebra (σ : X ⟶ Spec (.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  (chartScalarMap σ U).toAlgebra

/-- Local finite type of the actual structural morphism gives finite
type of each actual affine chart's original scalar action. -/
theorem chartScalarMap_finiteType (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ]
    (U : X.Opens) (hU : IsAffineOpen U) : (chartScalarMap σ U).FiniteType := by
  have hs := σ.finiteType_appLE (isAffineOpen_top (Spec (.of k))) hU (by simp)
  have hk : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
  exact hs.comp hk

theorem chartScalarAlgebra_finiteType (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
    Algebra.FiniteType k Γ(X, U) := by
  exact chartScalarMap_finiteType σ U hU

variable [CharZero k] [IsIntegral X]

/-- Every actual nonempty affine chart has finite normalization in its
actual original scheme function field, with all scalar actions constructed. -/
theorem originalAffineChart_integralClosure_finite
    (σ : X ⟶ Spec (.of k)) [LocallyOfFiniteType σ]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Module.Finite Γ(X, U) (integralClosure Γ(X, U) X.functionField) := by
  letI : Algebra k Γ(X, U) := chartScalarAlgebra σ U
  letI : Algebra.FiniteType k Γ(X, U) := chartScalarAlgebra_finiteType σ U hU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact finiteType_integralClosure_finite k Γ(X, U) X.functionField

end ChenRanks
