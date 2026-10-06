import ChenRanks.CurveRestriction
import ChenRanks.LogarithmicDifferentials

/-!
# Actual differential transport along the constructed original-field comparison

The map is the native differential map for the actual field isomorphism.
Its bijectivity is proved from genuine scalar-compatible field structures;
it is not a supplied identification of differential spaces. The actual
universal derivatives and logarithmic generators commute with this map.
-/

noncomputable section

namespace ChenRanks

variable {k F G : Type*} [Field k] [CharZero k] [Field F] [Field G]
  [Algebra k F] [Algebra k G]

/-- The actual transported scalar action on the target field. -/
abbrev fieldEquivTargetAlgebra (e : F ≃ₐ[k] G) : Algebra F G :=
  e.toRingHom.toAlgebra

omit [CharZero k] in
/-- The transported action respects the original constant field. -/
theorem fieldEquivTargetScalarTower (e : F ≃ₐ[k] G) :
    letI : Algebra F G := fieldEquivTargetAlgebra e
    IsScalarTower k F G := by
  letI : Algebra F G := fieldEquivTargetAlgebra e
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (e.commutes c).symm

omit [CharZero k] in
/-- The actual isomorphism supplies finite type, rather than requiring it. -/
theorem fieldEquivTargetAlgebra_finiteType (e : F ≃ₐ[k] G) :
    letI : Algebra F G := fieldEquivTargetAlgebra e
    Algebra.FiniteType F G := by
  letI : Algebra F G := fieldEquivTargetAlgebra e
  letI : Module.Finite F G := RingHom.Finite.of_surjective e.toRingHom e.surjective
  infer_instance

/-- The native actual differential map is a constant-field linear equivalence. -/
def differentialFieldLinearEquiv (e : F ≃ₐ[k] G) : Ω[F⁄k] ≃ₗ[k] Ω[G⁄k] := by
  letI : Algebra F G := fieldEquivTargetAlgebra e
  letI : IsScalarTower k F G := fieldEquivTargetScalarTower e
  letI : Algebra.FiniteType F G := fieldEquivTargetAlgebra_finiteType e
  exact LinearEquiv.ofBijective ((KaehlerDifferential.map k k F G).restrictScalars k)
    ⟨curveRestriction_map_injective k F G,
      KaehlerDifferential.map_surjective_of_surjective k k F G e.surjective⟩

/-- The constructed comparison carries the actual universal derivative. -/
@[simp]
theorem differentialFieldLinearEquiv_D (e : F ≃ₐ[k] G) (x : F) :
    differentialFieldLinearEquiv e (KaehlerDifferential.D k F x) =
      KaehlerDifferential.D k G (e x) := by
  letI : Algebra F G := fieldEquivTargetAlgebra e
  letI : IsScalarTower k F G := fieldEquivTargetScalarTower e
  exact KaehlerDifferential.map_D k k F G x

/-- The same actual map respects multiplication by original rational functions. -/
theorem differentialFieldLinearEquiv_smul (e : F ≃ₐ[k] G) (x : F) (ω : Ω[F⁄k]) :
    differentialFieldLinearEquiv e (x • ω) = e x • differentialFieldLinearEquiv e ω := by
  letI : Algebra F G := fieldEquivTargetAlgebra e
  letI : IsScalarTower k F G := fieldEquivTargetScalarTower e
  exact (KaehlerDifferential.map k k F G).map_smul x ω

/-- Original logarithmic generators are actual logarithmic generators on the model. -/
@[simp]
theorem differentialFieldLinearEquiv_logarithmic (e : F ≃ₐ[k] G) (u : Fˣ) :
    differentialFieldLinearEquiv e (logarithmicDifferential k F u) =
      logarithmicDifferential k G (Units.map e.toRingHom.toMonoidHom u) := by
  simp only [logarithmicDifferential, differentialFieldLinearEquiv_smul,
    differentialFieldLinearEquiv_D, map_inv₀]
  rfl

end ChenRanks
