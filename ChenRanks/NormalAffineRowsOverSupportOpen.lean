import ChenRanks.AffineHeightOneChartIndependence
import ChenRanks.HorizontalAffineHeightOneResidueDetection
import ChenRanks.FiniteVerticalSupportOpen

/-!
# All actual height-one rows after deleting the actual vertical support

A finite actual normal affine cover of the source constructs an actual
nonempty base open by deleting the actual nongeneric images of all the
nonzero orders of the original rational functions. At any actual
height-one point of any actual normal affine chart above this open, a
mixed differential relation has zero order rows. Horizontal points are
handled by the proved actual residue construction. At nonhorizontal
points the actual orders are zero: choose an original covering chart
at the same actual point and use the proved actual chart independence.

Neither the existence of the open, the completeness of a chosen divisor
list, nor an order-kernel condition is a hypothesis. The finite family
is explicitly required to be an actual cover. Actual structural maps,
finite type, normal affine chart rings, and actual curve-field pullback
witnesses are retained; the model construction supplies these objects.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

namespace ChenRanks

universe u

variable {k : Type u} [Field k] [CharZero k]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual constructed avoidance open makes every actual height-one
point row vanish, including points on new affine charts after shrinking.
The comparison uses the same actual point and the same original field. -/
theorem normalAffinePoint_mixed_relation_zero_rows_over_support_open
    (σX : X ⟶ Spec (.of k)) [LocallyOfFiniteType σX]
    (σY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsDominant f]
    (hstructure : f ≫ σY = σX)
    {c : Type*} [Fintype c] (U : c → X.Opens)
    [∀ d, Nonempty (U d)] (hAffine : ∀ d, IsAffineOpen (U d))
    [∀ d, IsNoetherianRing Γ(X, U d)]
    [∀ d, IsIntegrallyClosed Γ(X, U d)]
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    {j : Type*} [Fintype j] :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    ∀ (P : Submodule k Ω[X.functionField⁄k]) [FiniteDimensional k P],
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄k],
        KaehlerDifferential.map k k Y.functionField X.functionField η =
          (ω : Ω[X.functionField⁄k])) →
      ∀ (F : j → X.functionFieldˣ)
        (β : Fin (Module.finrank k P) → j → k),
      (∑ i, ∑ a, algebraMap k X.functionField (β i a) •
        exteriorWedge (k := X.functionField)
          (logarithmicDifferential k X.functionField (F a))
          (Module.finBasis k P i : Ω[X.functionField⁄k])) = 0 →
      ∀ (V : X.Opens) (hV : IsAffineOpen V)
        [IsNoetherianRing Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
        (x : V),
      f x ∈ actualVerticalSupportAvoidanceOpen f U hAffine F →
      ∀ hh : (hV.primeIdealOf x).asIdeal.height = 1,
      letI : Nonempty V := ⟨x⟩
      letI : IsFractionRing Γ(X, V) X.functionField :=
        functionField_isFractionRing_of_isAffineOpen X V hV
      ∀ i, ∑ a, β i a *
        (heightOnePrimeOrder Γ(X, V) X.functionField
          (hV.primeIdealOf x).asIdeal (hV.primeIdealOf x).isPrime hh
          (F a : X.functionField) : k) = 0 := by
  classical
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro P _ hpull F β hrelation V hV _ _ x hxW hh
  letI : Nonempty V := ⟨x⟩
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  by_cases hx : f x = genericPoint Y
  · exact horizontal_normalAffineHeightOne_mixed_relation_has_zero_order_coefficients
      σX σY f hstructure V hV x hx hh P hpull F β hrelation
  · obtain ⟨d, hxd⟩ := Opens.mem_iSup.mp (hcover (by trivial : (x : X) ∈ (⊤ : X.Opens)))
    let xd : U d := ⟨x, hxd⟩
    have hhd : ((hAffine d).primeIdealOf xd).asIdeal.height = 1 := by
      exact (actualAffinePointHeight_eq (U d) V (hAffine d) hV x hxd x.property).trans hh
    let pd : {p : Ideal Γ(X, U d) // p.IsPrime ∧ p.height = 1} :=
      ⟨((hAffine d).primeIdealOf xd).asIdeal,
        ((hAffine d).primeIdealOf xd).isPrime, hhd⟩
    have hpoint : (hAffine d).fromSpec ⟨pd.val, pd.property.1⟩ = (x : X) :=
      (hAffine d).fromSpec_primeIdealOf xd
    have hzero := actual_order_zero_of_nonhorizontal_prime_in_avoidance
      f U hAffine F d pd (by simpa only [hpoint] using hx)
      (by simpa only [hpoint] using hxW)
    letI : IsFractionRing Γ(X, U d) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X (U d) (hAffine d)
    have hzV (a : j) : heightOnePrimeOrder Γ(X, V) X.functionField
        (hV.primeIdealOf x).asIdeal (hV.primeIdealOf x).isPrime hh
        (F a : X.functionField) = 0 := by
      have hord := actualAffineHeightOneOrder_eq (U d) V (hAffine d) hV
        x hxd x.property hhd hh (F a)
      exact hord.symm.trans (hzero a)
    intro i
    simp only [hzV, Int.cast_zero, mul_zero, Finset.sum_const_zero]

/-- Every actual prime row on any actual normal affine chart contained
in the constructed inverse-image open vanishes. This is the full row
domain required by the proper generic-fibre argument. -/
theorem normalAffinePrime_mixed_relation_zero_rows_over_support_open
    (σX : X ⟶ Spec (.of k)) [LocallyOfFiniteType σX]
    (σY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsDominant f]
    (hstructure : f ≫ σY = σX)
    {c : Type*} [Fintype c] (U : c → X.Opens)
    [∀ d, Nonempty (U d)] (hAffine : ∀ d, IsAffineOpen (U d))
    [∀ d, IsNoetherianRing Γ(X, U d)]
    [∀ d, IsIntegrallyClosed Γ(X, U d)]
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    {j : Type*} [Fintype j] :
    letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
    letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
    letI : Algebra Y.functionField X.functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      functionFieldScalarTower_of_structure_square σX σY f hstructure
    ∀ (P : Submodule k Ω[X.functionField⁄k]) [FiniteDimensional k P],
      (∀ ω : P, ∃ η : Ω[Y.functionField⁄k],
        KaehlerDifferential.map k k Y.functionField X.functionField η =
          (ω : Ω[X.functionField⁄k])) →
      ∀ (F : j → X.functionFieldˣ)
        (β : Fin (Module.finrank k P) → j → k),
      (∑ i, ∑ a, algebraMap k X.functionField (β i a) •
        exteriorWedge (k := X.functionField)
          (logarithmicDifferential k X.functionField (F a))
          (Module.finBasis k P i : Ω[X.functionField⁄k])) = 0 →
      ∀ (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
        [IsNoetherianRing Γ(X, V)] [IsIntegrallyClosed Γ(X, V)],
      V ≤ f ⁻¹ᵁ actualVerticalSupportAvoidanceOpen f U hAffine F →
      ∀ (p : Ideal Γ(X, V)) (hp : p.IsPrime) (hh : p.height = 1),
      letI : IsFractionRing Γ(X, V) X.functionField :=
        functionField_isFractionRing_of_isAffineOpen X V hV
      ∀ i, ∑ a, β i a *
        (heightOnePrimeOrder Γ(X, V) X.functionField p hp hh
          (F a : X.functionField) : k) = 0 := by
  classical
  letI : Algebra k Y.functionField := structureFunctionFieldAlgebra σY
  letI : Algebra k X.functionField := structureFunctionFieldAlgebra σX
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : IsScalarTower k Y.functionField X.functionField :=
    functionFieldScalarTower_of_structure_square σX σY f hstructure
  intro P _ hpull F β hrelation V hV _ _ _ hVW p hp hh
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  let x : V := hV.isoSpec.inv ⟨p, hp⟩
  have hpx : hV.primeIdealOf x = (⟨p, hp⟩ : PrimeSpectrum Γ(X, V)) := by
    change hV.isoSpec.hom (hV.isoSpec.inv ⟨p, hp⟩) = ⟨p, hp⟩
    rw [← Scheme.Hom.comp_apply, hV.isoSpec.inv_hom_id]
    rfl
  have hheight : (hV.primeIdealOf x).asIdeal.height = 1 := by
    simpa only [hpx] using hh
  have hrows := normalAffinePoint_mixed_relation_zero_rows_over_support_open
    σX σY f hstructure U hAffine hcover P hpull F β hrelation V hV x
    (hVW x.property) hheight
  simpa only [hpx] using hrows

end ChenRanks
