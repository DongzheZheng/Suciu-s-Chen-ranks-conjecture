import ChenRanks.AffinePivotLowDegree
import ChenRanks.LogarithmicResidueCoefficients

/-!
# Actual divisor-class coefficient sums for affine polynomial logarithms

For a finite family of actual nonzero polynomials of total degree at most
one, a true logarithmic relation has coefficient sum zero on each actual
nonconstant divisor class. A selected degree-one polynomial gives a true
height-one principal prime. Its actual prime-localization DVR, formal
smoothness, and one-form residue are all constructed from the polynomial
ring. A polynomial divisible by the selected polynomial is a nonzero
constant multiple, so its actual order is the same; every other member is
a true local unit and has order zero. The selected order is genuinely
nonzero and is cancelled after the actual residue calculation.

The family may have repeated divisors or nonzero constant members. There
is no distinctness or logarithmic-independence assumption. This is not
yet the affine-flat block identification or the OS quadratic-kernel theorem.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

section ActualAffinePolynomialField

variable (k σ : Type*) [Field k]

instance affinePolynomialFractionField_baseAlgebra :
    Algebra k (FractionRing (MvPolynomial σ k)) :=
  ((algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))).comp
    MvPolynomial.C).toAlgebra

instance affinePolynomialFractionField_baseSMul :
    SMul k (FractionRing (MvPolynomial σ k)) :=
  (affinePolynomialFractionField_baseAlgebra k σ).toSMul

instance affinePolynomialFractionField_baseModule :
    Module k (FractionRing (MvPolynomial σ k)) := Algebra.toModule

instance affinePolynomialFractionField_baseScalarComm :
    SMulCommClass k k (FractionRing (MvPolynomial σ k)) where
  smul_comm c e f := by
    change algebraMap k (FractionRing (MvPolynomial σ k)) c *
        (algebraMap k (FractionRing (MvPolynomial σ k)) e * f) =
      algebraMap k (FractionRing (MvPolynomial σ k)) e *
        (algebraMap k (FractionRing (MvPolynomial σ k)) c * f)
    exact mul_left_comm _ _ _

instance affinePolynomialFractionField_baseScalarTower :
    IsScalarTower k k (FractionRing (MvPolynomial σ k)) where
  smul_assoc a b x := by
    change algebraMap k (FractionRing (MvPolynomial σ k)) (a * b) * x =
      algebraMap k (FractionRing (MvPolynomial σ k)) a *
        (algebraMap k (FractionRing (MvPolynomial σ k)) b * x)
    rw [map_mul, mul_assoc]

instance affinePolynomialFractionField_constantDifferentialModule :
    Module k Ω[FractionRing (MvPolynomial σ k)⁄k] :=
  KaehlerDifferential.module' k (FractionRing (MvPolynomial σ k))

instance affinePolynomialFractionField_polynomialModule :
    Module (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) :=
  Algebra.toModule

instance affinePolynomialFractionField_polynomialSMul :
    SMul (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) :=
  (inferInstance : Algebra (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))).toSMul

instance affinePolynomialFractionField_baseTower :
    IsScalarTower k (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := MvPolynomial σ k)
    (A := FractionRing (MvPolynomial σ k)) fun _ ↦ rfl

/-- The actual polynomial fraction, packaged as its genuine nonzero unit. -/
def affinePolynomialFractionUnit (q : MvPolynomial σ k) (hq : q ≠ 0) :
    (FractionRing (MvPolynomial σ k))ˣ :=
  Units.mk0 (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) q)
    ((map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ k)
      (FractionRing (MvPolynomial σ k)))).mpr hq)

private theorem affinePolynomial_irreducible_of_degree_one
    (g : MvPolynomial σ k) (hg : g.totalDegree = 1) : Irreducible g := by
  apply MvPolynomial.irreducible_of_totalDegree_eq_one hg
  intro r hr
  by_cases hz : r = 0
  · subst r
    have hgz : g = 0 := by
      apply MvPolynomial.ext
      intro m
      exact zero_dvd_iff.mp (hr m)
    simp only [hgz, MvPolynomial.totalDegree_zero] at hg
    omega
  · exact isUnit_iff_ne_zero.mpr hz

end ActualAffinePolynomialField

section ConstantMultipleOrders

variable (k S F : Type*) [Field k] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Field F]
  [Algebra k S] [Algebra k F] [Algebra S F] [IsScalarTower k S F] [IsFractionRing S F]

/-- Multiplication by a nonzero actual base-field constant leaves the
actual local DVR order unchanged, because its actual local lift is a unit. -/
theorem localDVRUnitOrder_eq_of_constant_multiple
    (a : k) (ha : a ≠ 0) (f g : Fˣ)
    (h : (f : F) = algebraMap k F a * (g : F)) :
    localDVRUnitOrder S F f = localDVRUnitOrder S F g := by
  let u : Sˣ := Units.map (algebraMap k S).toMonoidHom (Units.mk0 a ha)
  have hf : f = Units.map (algebraMap S F).toMonoidHom u * g := by
    apply Units.ext
    change (f : F) = algebraMap S F (algebraMap k S a) * (g : F)
    rw [← IsScalarTower.algebraMap_apply k S F]
    exact h
  have huorder : localDVRUnitOrder S F (Units.map (algebraMap S F).toMonoidHom u) = 0 :=
    localDVRUnitOrder_localUnit S F u
  rw [hf, localDVRUnitOrder_mul, huorder, zero_add]

/-- A true fraction-field unit that is the image of an actual local
unit has zero actual DVR order. The local unit is obtained from IsUnit. -/
theorem localDVRUnitOrder_zero_of_isUnit_image
    (x : S) (hx : IsUnit x) (f : Fˣ)
    (h : (f : F) = algebraMap S F x) : localDVRUnitOrder S F f = 0 := by
  have hf : f = Units.map (algebraMap S F).toMonoidHom hx.unit := by
    apply Units.ext
    change (f : F) = algebraMap S F (hx.unit : S)
    rw [hx.unit_spec]
    exact h
  rw [hf]
  exact localDVRUnitOrder_localUnit S F hx.unit

end ConstantMultipleOrders

section ActualDivisorClassResidue

variable (k σ : Type*) [Field k] [CharZero k] [Fintype σ]
  {ι : Type*} [Fintype ι]

local instance affinePolynomialClasses_propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

set_option maxHeartbeats 400000 in
/-- A true finite logarithmic relation forces coefficient sum zero on
each actual nonconstant affine-polynomial divisor class. The class is
specified by genuine polynomial divisibility, not a supplied partition. -/
theorem affinePolynomialLogarithmicRelation_divisorClass_sum_zero
    (q : ι → MvPolynomial σ k) (hq : ∀ i, q i ≠ 0)
    (hdegree : ∀ i, (q i).totalDegree ≤ 1) (c : ι → k)
    (hrelation : (∑ i, c i • logarithmicDifferential k (FractionRing (MvPolynomial σ k))
      (affinePolynomialFractionUnit k σ (q i) (hq i))) = 0)
    (i₀ : ι) (hi₀ : (q i₀).totalDegree = 1) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ q i₀ ∣ q i), c i) = 0 := by
  classical
  let R := MvPolynomial σ k
  let F := FractionRing R
  let p : Ideal R := Ideal.span {q i₀}
  letI : p.IsPrime := (Ideal.span_singleton_prime (hq i₀)).mpr
    (affinePolynomial_irreducible_of_degree_one k σ (q i₀) hi₀).prime
  letI : p.IsPrincipal := by dsimp only [p]; infer_instance
  have hheight : p.height = 1 := by
    have hself : p ∈ p.minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton p
    have hle : p.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes p p hself
    have hlt : (⊥ : Ideal R) < p := by
      apply bot_lt_iff_ne_bot.mpr
      intro hp
      exact hq i₀ (Ideal.mem_bot.mp (hp ▸ Ideal.mem_span_singleton_self (q i₀)))
    have hpos : (0 : ℕ∞) < p.height := by
      simpa only [Ideal.height_bot] using Ideal.height_strict_mono_of_is_prime hlt
    have hge : (1 : ℕ∞) ≤ p.height := by
      simpa using (ENat.add_one_le_iff (show (0 : ℕ∞) ≠ ⊤ by simp)).mpr hpos
    exact le_antisymm hle hge
  let S := primeLocalizationInFractionField R F p (inferInstance : p.IsPrime)
  letI : CommRing S := Subalgebra.toCommRing _
  letI : IsDomain S := Subalgebra.isDomain _
  letI : Algebra R S := Subalgebra.algebra _
  letI : Algebra S F := Subalgebra.toAlgebra _
  letI : Module R S := Algebra.toModule
  letI : SMul R S := (inferInstance : Algebra R S).toSMul
  letI : Module S F := Algebra.toModule
  letI : SMul S F := (inferInstance : Algebra S F).toSMul
  letI : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq
    (R := R) (S := S) (A := F) fun _ ↦ rfl
  letI : Algebra k S := ((algebraMap R S).comp MvPolynomial.C).toAlgebra
  letI : Module k S := Algebra.toModule
  letI : SMul k S := (inferInstance : Algebra k S).toSMul
  letI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq
    (R := k) (S := R) (A := S) fun _ ↦ rfl
  letI : IsScalarTower k S F := IsScalarTower.of_algebraMap_eq
    (R := k) (S := S) (A := F) fun _ ↦ rfl
  letI : SMulCommClass k S F := {
    smul_comm := fun a b x ↦ by
      change algebraMap k F a * (algebraMap S F b * x) =
        algebraMap S F b * (algebraMap k F a * x)
      exact mul_left_comm _ _ _ }
  letI : Module S Ω[F⁄k] := KaehlerDifferential.module' k F (R' := S)
  letI : SMul S Ω[F⁄k] := (inferInstance : Module S Ω[F⁄k]).toSMul
  letI : IsScalarTower k S Ω[F⁄k] :=
    KaehlerDifferential.isScalarTower_of_tower k F (R₁ := k) (R₂ := S)
  letI : IsLocalization.AtPrime S p := by
    change IsLocalization p.primeCompl
      (Localization.subalgebra F p.primeCompl p.primeCompl_le_nonZeroDivisors)
    infer_instance
  letI : IsFractionRing S F := by
    change IsFractionRing
      (Localization.subalgebra F p.primeCompl p.primeCompl_le_nonZeroDivisors) F
    infer_instance
  letI : IsDiscreteValuationRing S :=
    height_one_primeLocalization_isDiscreteValuationRing R F p inferInstance hheight
  letI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_isLocalization S p.primeCompl
  letI : Algebra.EssFiniteType k S := Algebra.EssFiniteType.comp k R S
  letI : Algebra.FormallySmooth k S := polynomialLocalization_formallySmooth k σ S p.primeCompl
  let f : ι → Fˣ := fun i ↦ affinePolynomialFractionUnit k σ (q i) (hq i)
  let n : ℤ := localDVRUnitOrder S F (f i₀)
  have hn : n ≠ 0 := by
    intro hz
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
    obtain ⟨u, hu⟩ := exists_fraction_unit_uniformizer_order_factorization S F π hπ (f i₀)
    have hfield : algebraMap R F (q i₀) = algebraMap S F (u : S) := by
      have hh := congrArg (fun v : Fˣ ↦ (v : F)) hu
      rw [show localDVRUnitOrder S F (f i₀) = 0 from hz] at hh
      simpa only [f, affinePolynomialFractionUnit, Units.val_mk0,
        zpow_zero, mul_one, Units.coe_map] using hh
    have hlocal : algebraMap R S (q i₀) = (u : S) := by
      apply IsFractionRing.injective S F
      exact hfield
    have hnot : q i₀ ∉ p :=
      (IsLocalization.AtPrime.isUnit_to_map_iff S p (q i₀)).mp
        (hlocal.symm ▸ u.isUnit)
    exact hnot (Ideal.mem_span_singleton_self (q i₀))
  have horder (i : ι) : localDVRUnitOrder S F (f i) = if q i₀ ∣ q i then n else 0 := by
    by_cases hdiv : q i₀ ∣ q i
    · rw [if_pos hdiv]
      obtain ⟨a, ha⟩ := constant_multiple_of_degree_one_dvd (q i₀) (q i) hi₀ (hdegree i) hdiv
      have ha₀ : a ≠ 0 := by
        intro hz
        exact hq i (by simpa only [hz, map_zero, zero_mul] using ha)
      have hf : (f i : F) = algebraMap k F a * (f i₀ : F) := by
        change algebraMap R F (q i) = algebraMap k F a * algebraMap R F (q i₀)
        rw [ha, map_mul]
        rfl
      exact localDVRUnitOrder_eq_of_constant_multiple k S F a ha₀ (f i) (f i₀) hf
    · rw [if_neg hdiv]
      have hu : IsUnit (algebraMap R S (q i)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff S p (q i)).mpr
          (by change q i ∉ Ideal.span {q i₀}; rwa [Ideal.mem_span_singleton])
      have hf : (f i : F) = algebraMap S F (algebraMap R S (q i)) := by
        change algebraMap R F (q i) = algebraMap S F (algebraMap R S (q i))
        exact (IsScalarTower.algebraMap_apply R S F (q i)).symm
      exact localDVRUnitOrder_zero_of_isUnit_image S F (algebraMap R S (q i)) hu (f i) hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hlocalrelation : (∑ i, algebraMap k S (c i) • logarithmicDifferential k F (f i)) = 0 := by
    simpa only [algebraMap_smul S] using hrelation
  have hr := logarithmicOneForm_constant_relation_orders k S F Finset.univ π hπ c f hlocalrelation
  have hsum : (∑ i, c i * (localDVRUnitOrder S F (f i) : k)) =
      (∑ i ∈ Finset.univ.filter (fun i ↦ q i₀ ∣ q i), c i) * (n : k) := by
    rw [Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [horder]
    by_cases hi : q i₀ ∣ q i <;> simp only [hi, ↓reduceIte, Int.cast_zero, mul_zero]
  have hs : (∑ i ∈ Finset.univ.filter (fun i ↦ q i₀ ∣ q i), c i) * (n : k) = 0 :=
    hsum.symm.trans hr
  exact (mul_eq_zero.mp hs).resolve_right (Int.cast_ne_zero.mpr hn)

end ActualDivisorClassResidue

end ChenRanks
