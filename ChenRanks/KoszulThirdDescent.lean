import ChenRanks.KoszulThirdAlternating

/-! Genuine descent of the third alternating formula to the actual exterior power. -/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

section ScalarExtension

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [_root_.Module R M]
variable [AddCommGroup N] [_root_.Module R N] [_root_.Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]

/-- The genuine polynomial-linear extension of an arbitrary base-linear map.
Its pure-tensor calculation is established before any exterior formula is supplied. -/
def extendScalarLinear (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N :=
  AlgebraTensorModule.lift (R := R) (A := A) (M := A) (N := M) (P := N)
    (LinearMap.toSpanSingleton A (M →ₗ[R] N) f)

@[simp] theorem extendScalarLinear_tmul (f : M →ₗ[R] N) (a : A) (m : M) :
    extendScalarLinear f (a ⊗ₜ[R] m) = a • f m := by
  simp only [extendScalarLinear, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply]

end ScalarExtension

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

/-- Cache the genuine coefficient action on the actual second tensor term. -/
local instance canonicalC2CoefficientModule : _root_.Module (S k V) (C2 k V) :=
  TensorProduct.leftModule (R := k) (R'' := S k V) (M := S k V) (N := ⋀[k]^2 V)

/-- Genuine descent of the actual alternating formula to the third exterior power. -/
def delta3Linear : (⋀[k]^3 V) →ₗ[k] C2 k V :=
  exteriorPower.alternatingMapLinearEquiv (delta3Alternating k V)

@[simp] theorem delta3Linear_wedge (a : Fin 3 → V) :
    delta3Linear k V (exteriorPower.ιMulti k 3 a) =
      SymmetricAlgebra.ι k V (a 0) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 1) (a 2)) -
        SymmetricAlgebra.ι k V (a 1) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 0) (a 2)) +
          SymmetricAlgebra.ι k V (a 2) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 0) (a 1)) := by
  rw [delta3Linear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The genuine polynomial-linear coefficient map, kept separately typed. -/
def delta3CoefficientMap : S k V →ₗ[S k V] (⋀[k]^3 V) →ₗ[k] C2 k V :=
  LinearMap.toSpanSingleton (S k V) ((⋀[k]^3 V) →ₗ[k] C2 k V) (delta3Linear k V)

@[simp] theorem delta3CoefficientMap_apply (s : S k V) (w : ⋀[k]^3 V) :
    delta3CoefficientMap k V s w = s • delta3Linear k V w := by
  simp only [delta3CoefficientMap, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply]

/-- The actual third differential with the actual polynomial scalar action. -/
def delta3 : C3 k V →ₗ[S k V] C2 k V :=
  extendScalarLinear (delta3Linear k V)

@[simp] theorem delta3_tmul (s : S k V) (w : ⋀[k]^3 V) :
    delta3 k V (s ⊗ₜ[k] w) = s • delta3Linear k V w := by
  exact extendScalarLinear_tmul (delta3Linear k V) s w

end ChenRanks.Koszul
