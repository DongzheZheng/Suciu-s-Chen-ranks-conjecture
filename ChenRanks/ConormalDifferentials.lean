import Mathlib

/-!
# The actual split conormal map over a smooth residue field

The conormal map in this file is the actual map
`I/I² → (A/I) ⊗[A] Ω[A/C]`, sending the class of `x ∈ I` to `1 ⊗ dx`.
Its left inverse is obtained by lifting the identity of `A/I` through
the square-zero thickening `A/I²`, then using mathlib's proved
correspondence between sections of that thickening and retractions of
the actual conormal map.  No injectivity or residue detector is an input.

For a maximal ideal and a characteristic-zero constant field, essential
finite type of the actual quotient field supplies formal smoothness.
For an essentially finite-type local ring, the quotient theorem supplies
the required finite type of its actual residue field.

These results concern actual cotangent and Kähler modules before
localization.  They do not prove that `Ω[A/C] → Ω[Frac(A)/C]` is injective,
and do not yet define logarithmic one-form or two-form residues.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

section ActualConormalMap

variable (C A : Type*) [CommRing C] [CommRing A] [Algebra C A] (I : Ideal A)

/-- The actual derivative of an ideal element in the residue-field
base change of the Kähler module. -/
def quotientIdealToTensor : I →ₗ[A] (A ⧸ I) ⊗[A] Ω[A⁄C] where
  toFun x := (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D C A (x : A)
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, TensorProduct.tmul_add]
  map_smul' r x := by
    have hx : algebraMap A (A ⧸ I) (x : A) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr x.property
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, hx, TensorProduct.zero_tmul, add_zero, RingHom.id_apply]

/-- Products of actual ideal elements have zero image, so the derivative
really descends through `I/I²`. -/
theorem quotientIdealToTensor_mul (x y : I) :
    quotientIdealToTensor C A I (x * y) = 0 := by
  have hx : algebraMap A (A ⧸ I) (x : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr x.property
  have hy : algebraMap A (A ⧸ I) (y : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr y.property
  change (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D C A ((x : A) * (y : A)) = 0
  simp only [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, hx, hy,
    TensorProduct.zero_tmul, zero_add]

/-- The actual conormal map, defined on the genuine module `I/I²`.
It is the usual class-of-an-element-to-its-differential construction. -/
def quotientConormalMap : I.Cotangent →ₗ[A] (A ⧸ I) ⊗[A] Ω[A⁄C] :=
  Ideal.Cotangent.lift (quotientIdealToTensor C A I) (quotientIdealToTensor_mul C A I)

@[simp]
theorem quotientConormalMap_toCotangent (x : I) :
    quotientConormalMap C A I (I.toCotangent x) =
      (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D C A (x : A) := rfl

end ActualConormalMap

section SmoothTarget

variable (C A κ : Type*) [CommRing C] [CommRing A] [CommRing κ]
  [Algebra C A] [Algebra C κ] [Algebra A κ] [IsScalarTower C A κ]

/-- An actual formally smooth quotient has a retraction of its actual
kernel conormal map.  The proof constructs a section of the square-zero
thickening by formal smoothness, then uses the proved section/retraction
equivalence; it does not assume a splitting. -/
theorem exists_kernelConormal_retraction_of_formallySmooth
    [Algebra.FormallySmooth C κ] (hs : Function.Surjective (algebraMap A κ)) :
    ∃ l : κ ⊗[A] Ω[A⁄C] →ₗ[A] (RingHom.ker (algebraMap A κ)).Cotangent,
      l.comp (KaehlerDifferential.kerCotangentToTensor C A κ) = LinearMap.id := by
  let q : A →ₐ[C] κ := IsScalarTower.toAlgHom C A κ
  have hsq : Function.Surjective q.kerSquareLift := by
    intro z
    obtain ⟨a, ha⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  have hnil : IsNilpotent (RingHom.ker q.kerSquareLift.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  let σ : κ →ₐ[C] A ⧸ (RingHom.ker q.toRingHom) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id C κ) q.kerSquareLift hsq hnil
  have hσ : q.kerSquareLift.comp σ = AlgHom.id C κ :=
    Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id C κ) q.kerSquareLift hsq hnil
  let retraction :=
    (retractionKerCotangentToTensorEquivSection (R := C) hs).symm ⟨σ, hσ⟩
  exact ⟨retraction.val, retraction.property⟩

/-- The generator formula for the actual retraction.  This version makes
the canonical identification `ker(A → A/I) = I` transparent. -/
theorem exists_kernelConormal_generator_retraction_of_formallySmooth
    [Algebra.FormallySmooth C κ] (hs : Function.Surjective (algebraMap A κ)) :
    ∃ l : κ ⊗[A] Ω[A⁄C] →ₗ[A] (RingHom.ker (algebraMap A κ)).Cotangent,
      ∀ x : RingHom.ker (algebraMap A κ),
        l ((1 : κ) ⊗ₜ[A] KaehlerDifferential.D C A (x : A)) =
          (RingHom.ker (algebraMap A κ)).toCotangent x := by
  obtain ⟨l, hl⟩ := exists_kernelConormal_retraction_of_formallySmooth C A κ hs
  refine ⟨l, fun x ↦ ?_⟩
  simpa only [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent,
    LinearMap.id_apply] using
    LinearMap.congr_fun hl ((RingHom.ker (algebraMap A κ)).toCotangent x)

end SmoothTarget

section ActualSmoothQuotient

variable (C A : Type*) [CommRing C] [CommRing A] [Algebra C A] (I : Ideal A)

/-- A retraction on the actual quotient ideal cotangent module.  Only
formal smoothness of the actual quotient is required in this intermediate
theorem; the characteristic-zero field application derives it below. -/
theorem exists_quotientConormal_retraction_of_formallySmooth
    [Algebra.FormallySmooth C (A ⧸ I)] :
    ∃ l : (A ⧸ I) ⊗[A] Ω[A⁄C] →ₗ[A] I.Cotangent,
      l.comp (quotientConormalMap C A I) = LinearMap.id := by
  have H := exists_kernelConormal_generator_retraction_of_formallySmooth C A (A ⧸ I)
    (Ideal.Quotient.mk_surjective)
  change ∃ l : (A ⧸ I) ⊗[A] Ω[A⁄C] →ₗ[A] (RingHom.ker (Ideal.Quotient.mk I)).Cotangent,
    ∀ x : RingHom.ker (Ideal.Quotient.mk I),
      l ((1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D C A (x : A)) =
        (RingHom.ker (Ideal.Quotient.mk I)).toCotangent x at H
  rw [Ideal.mk_ker] at H
  obtain ⟨l, hl⟩ := H
  refine ⟨l, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  simpa only [LinearMap.comp_apply, quotientConormalMap_toCotangent,
    LinearMap.id_apply] using hl x

end ActualSmoothQuotient

section CharacteristicZeroQuotientField

variable (C A : Type*) [Field C] [CharZero C] [CommRing A] [Algebra C A]
  (I : Ideal A) [I.IsMaximal] [Algebra.EssFiniteType C (A ⧸ I)]

/-- Essential finite type of the actual characteristic-zero quotient
field proves the existence of a genuine conormal left inverse.  Formal
smoothness is derived from perfectness, not supplied as a new hypothesis. -/
theorem exists_quotientConormal_retraction :
    ∃ l : (A ⧸ I) ⊗[A] Ω[A⁄C] →ₗ[A] I.Cotangent,
      l.comp (quotientConormalMap C A I) = LinearMap.id := by
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  letI : Algebra.FormallySmooth C (A ⧸ I) := inferInstance
  exact exists_quotientConormal_retraction_of_formallySmooth C A I

/-- An actual retraction chosen from the proved square-zero lifting
construction.  Its defining existence theorem has already been proved. -/
def quotientConormalRetraction : (A ⧸ I) ⊗[A] Ω[A⁄C] →ₗ[A] I.Cotangent :=
  (exists_quotientConormal_retraction C A I).choose

@[simp]
theorem quotientConormalRetraction_comp :
    (quotientConormalRetraction C A I).comp (quotientConormalMap C A I) =
      LinearMap.id :=
  (exists_quotientConormal_retraction C A I).choose_spec

/-- The actual conormal map has an actual left inverse. -/
theorem quotientConormalRetraction_leftInverse :
    Function.LeftInverse (quotientConormalRetraction C A I) (quotientConormalMap C A I) := by
  intro x
  exact LinearMap.congr_fun (quotientConormalRetraction_comp C A I) x

/-- The actual conormal map is injective; injectivity is a conclusion. -/
theorem quotientConormalMap_injective : Function.Injective (quotientConormalMap C A I) :=
  (quotientConormalRetraction_leftInverse C A I).injective

/-- A nonzero actual conormal class gives a nonzero residue-field
base-changed differential.  This does not assert localization injectivity. -/
theorem quotientConormal_tmul_d_ne_zero (x : I) (hx : I.toCotangent x ≠ 0) :
    (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D C A (x : A) ≠ 0 := by
  intro h
  apply hx
  apply quotientConormalMap_injective C A I
  simpa only [quotientConormalMap_toCotangent, map_zero] using h

end CharacteristicZeroQuotientField

section ActualLocalRing

variable (C A : Type*) [Field C] [CharZero C] [CommRing A] [Algebra C A]
  [IsLocalRing A] [Algebra.EssFiniteType C A]

/-- The conormal map of the actual maximal ideal of a local ring,
with its actual residue field as coefficient field. -/
def localConormalMap : IsLocalRing.CotangentSpace A →ₗ[A]
    IsLocalRing.ResidueField A ⊗[A] Ω[A⁄C] :=
  quotientConormalMap C A (IsLocalRing.maximalIdeal A)

/-- An essentially finite-type local ring has an actual conormal
retraction over characteristic zero.  Quotient finite type and residue
field formal smoothness are derived from the input local ring. -/
theorem exists_localConormal_retraction :
    ∃ l : IsLocalRing.ResidueField A ⊗[A] Ω[A⁄C] →ₗ[A] IsLocalRing.CotangentSpace A,
      l.comp (localConormalMap C A) = LinearMap.id := by
  letI : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  exact exists_quotientConormal_retraction C A (IsLocalRing.maximalIdeal A)

/-- Injectivity for the actual local-ring conormal map, with no
injectivity hypothesis and no separate residue-field smoothness input. -/
theorem localConormalMap_injective : Function.Injective (localConormalMap C A) := by
  letI : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  exact quotientConormalMap_injective C A (IsLocalRing.maximalIdeal A)

end ActualLocalRing

end ChenRanks
