import ChenRanks.FiniteAlgebraFractionField

/-!
# Actual finite normalization of characteristic-zero finite-type domains

Actual Noether normalization supplies a finite injective polynomial
algebra inclusion. The actual fraction extension is constructed by
finite localization, rather than assumed. Integrality transitivity
identifies the original ring's actual integral closure with an integral
closure over that polynomial algebra. The finite separable integral-
closure theorem then proves finiteness over the original ring.

This supplies normalization finiteness for actual finite-type affine
charts of the paper's graph model. Scheme-chart construction and the
actual normalization morphism remain separate steps.
-/

noncomputable section

namespace ChenRanks

variable (A R F : Type*) [CommRing A] [IsDomain A] [CharZero A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]
  [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra A F] [IsScalarTower A R F]

/-- A genuine finite algebra inclusion into the original domain implies
finite normalization in its original actual fraction field. -/
theorem finiteAlgebra_integralClosure_finite
    (hAR : Function.Injective (algebraMap A R)) :
    Module.Finite R (integralClosure R F) := by
  letI : Algebra (FractionRing A) F := finiteAlgebraFractionBaseAlgebra A R F hAR
  letI : IsScalarTower A (FractionRing A) F :=
    finiteAlgebraFractionBaseScalarTower A R F hAR
  letI : FiniteDimensional (FractionRing A) F :=
    finiteAlgebraFraction_finiteDimensional A R F hAR
  letI : Algebra.IsSeparable (FractionRing A) F := inferInstance
  let C := integralClosure R F
  letI : Algebra A C := inferInstance
  letI : IsScalarTower A R C := inferInstance
  letI : IsScalarTower A C F := inferInstance
  letI : Algebra.IsIntegral A R := inferInstance
  letI : IsIntegralClosure C A F :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          exact ⟨⟨x, hx.tower_top⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact isIntegral_trans (R := A) (y : F) y.property }
  letI : Module.Finite A C := IsIntegralClosure.finite A (FractionRing A) F C
  exact Module.Finite.of_restrictScalars_finite A R C

section ActualFiniteType

variable (k S K : Type*) [Field k] [CharZero k] [CommRing S] [IsDomain S]
  [Algebra k S] [Algebra.FiniteType k S]
  [Field K] [Algebra S K] [IsFractionRing S K]

include k

/-- The original actual characteristic-zero finite-type domain has finite
normalization in its original fraction field. No normalization-finiteness
or finite-fraction-extension hypothesis is an input. -/
theorem finiteType_integralClosure_finite : Module.Finite S (integralClosure S K) := by
  obtain ⟨n, g, hg, hfinite⟩ :=
    _root_.exists_finite_inj_algHom_of_fg k S
  let N := MvPolynomial (Fin n) k
  letI : Algebra N S := g.toRingHom.toAlgebra
  letI : Algebra N K := ((algebraMap S K).comp g.toRingHom).toAlgebra
  letI : IsScalarTower N S K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Module.Finite N S := RingHom.finite_algebraMap.mp hfinite
  exact finiteAlgebra_integralClosure_finite N S K hg

end ActualFiniteType

end ChenRanks
