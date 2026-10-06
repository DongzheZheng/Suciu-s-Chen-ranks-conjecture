import ChenRanks.TranscendentalDVR

/-!
# The actual local polynomial base of an actual DVR uniformizer

A nonzero nonunit in a domain over a field is transcendental over the
field: otherwise it would be integral and hence a unit.  For an actual
DVR uniformizer π this constructs the actual map C[t]_(t) → A, t ↦ π.
The map is proved injective and local, its actual maximal-ideal image is
exactly the actual maximal ideal of A, and the actual module is flat.
No smoothness, flatness or residue detector for A is an input.
-/

noncomputable section

open Polynomial IsLocalRing
open scoped Polynomial

namespace ChenRanks

variable (C A : Type*) [Field C] [CommRing A] [IsDomain A]
  [Algebra C A] [IsDiscreteValuationRing A]

omit [IsDiscreteValuationRing A] in
/-- An actual uniformizer cannot be algebraic over the original field. -/
theorem dvrUniformizer_transcendental (π : A) (hπ : Irreducible π) :
    Transcendental C π := by
  intro ha
  exact hπ.not_isUnit (ha.isIntegral.isUnit hπ.ne_zero)

/-- The actual residue of evaluation at the actual uniformizer is the
actual residue of its constant coefficient. -/
theorem dvrUniformizer_aeval_residue (π : A) (hπ : Irreducible π) (p : C[X]) :
    algebraMap A (ResidueField A) (aeval π p) =
      algebraMap C (ResidueField A) (p.coeff 0) := by
  let q : A →ₐ[C] ResidueField A := IsScalarTower.toAlgHom C A (ResidueField A)
  have hπzero : algebraMap A (ResidueField A) π = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have he : q.comp (aeval π) = aeval (0 : ResidueField A) := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply, aeval_X] using hπzero
  have hp := AlgHom.congr_fun he p
  change algebraMap A (ResidueField A) (aeval π p) = aeval (0 : ResidueField A) p at hp
  exact hp.trans (Polynomial.coeff_zero_eq_aeval_zero' p).symm

/-- Every denominator in the actual localization at `(t)` evaluates to
an actual unit of A, since its actual constant coefficient is nonzero. -/
theorem dvrUniformizer_denominator_isUnit (π : A) (hπ : Irreducible π)
    (p : (polynomialZeroIdeal C).primeCompl) : IsUnit (aeval π (p : C[X])) := by
  have hp : (p : C[X]).coeff 0 ≠ 0 := by
    intro hp0
    apply p.property
    exact Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr hp0)
  apply (residue_ne_zero_iff_isUnit (aeval π (p : C[X]))).mp
  change algebraMap A (ResidueField A) (aeval π (p : C[X])) ≠ 0
  rw [dvrUniformizer_aeval_residue C A π hπ]
  intro h
  apply hp
  apply (algebraMap C (ResidueField A)).injective
  simpa only [map_zero] using h

/-- The actual local polynomial base map sending its genuine
uniformizer to the genuine uniformizer π of A. -/
def dvrUniformizerBaseMap (π : A) (hπ : Irreducible π) :
    rationalFunctionZeroDVR C →ₐ[C] A :=
  IsLocalization.liftAlgHom (M := (polynomialZeroIdeal C).primeCompl)
    (f := aeval π) (dvrUniformizer_denominator_isUnit C A π hπ)

@[simp]
theorem dvrUniformizerBaseMap_algebraMap (π : A) (hπ : Irreducible π) (p : C[X]) :
    dvrUniformizerBaseMap C A π hπ
      (algebraMap C[X] (rationalFunctionZeroDVR C) p) = aeval π p := by
  exact IsLocalization.lift_eq (dvrUniformizer_denominator_isUnit C A π hπ) p

@[simp]
theorem dvrUniformizerBaseMap_uniformizer (π : A) (hπ : Irreducible π) :
    dvrUniformizerBaseMap C A π hπ (rationalFunctionZeroUniformizer C) = π := by
  rw [rationalFunctionZeroUniformizer, dvrUniformizerBaseMap_algebraMap, aeval_X]

/-- The actual localization map is injective by the proved
transcendence of π and the actual localization universal property. -/
theorem dvrUniformizerBaseMap_injective (π : A) (hπ : Irreducible π) :
    Function.Injective (dvrUniformizerBaseMap C A π hπ) := by
  change Function.Injective (IsLocalization.lift
    (dvrUniformizer_denominator_isUnit C A π hπ) : rationalFunctionZeroDVR C → A)
  apply (IsLocalization.lift_injective_iff
    (dvrUniformizer_denominator_isUnit C A π hπ)).mpr
  intro p q
  have hloc : Function.Injective (algebraMap C[X] (rationalFunctionZeroDVR C)) :=
    IsLocalization.injective (rationalFunctionZeroDVR C)
      (polynomialZeroIdeal C).primeCompl_le_nonZeroDivisors
  have heval : Function.Injective (aeval π : C[X] →ₐ[C] A) :=
    transcendental_iff_injective.mp (dvrUniformizer_transcendental C A π hπ)
  exact ⟨fun h ↦ congrArg (aeval π) (hloc h),
    fun h ↦ congrArg (algebraMap C[X] (rationalFunctionZeroDVR C)) (heval h)⟩

/-- The actual maximal-ideal image is exactly the actual maximal ideal
of A, proved from the two actual uniformizer formulas. -/
theorem dvrUniformizerBaseMap_maximalIdeal (π : A) (hπ : Irreducible π) :
    (maximalIdeal (rationalFunctionZeroDVR C)).map
      (dvrUniformizerBaseMap C A π hπ).toRingHom = maximalIdeal A := by
  rw [rationalFunctionZeroDVR_maximalIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {dvrUniformizerBaseMap C A π hπ
    (rationalFunctionZeroUniformizer C)} = maximalIdeal A
  rw [dvrUniformizerBaseMap_uniformizer, hπ.maximalIdeal_eq]

/-- The exact actual base map is a local ring homomorphism. -/
theorem dvrUniformizerBaseMap_isLocalHom (π : A) (hπ : Irreducible π) :
    IsLocalHom (dvrUniformizerBaseMap C A π hπ).toRingHom := by
  apply ((local_hom_TFAE (dvrUniformizerBaseMap C A π hπ).toRingHom).out 0 2 rfl rfl).mpr
  exact (dvrUniformizerBaseMap_maximalIdeal C A π hπ).le

/-- The actual A algebra structure over the actual polynomial DVR. -/
abbrev dvrUniformizerBaseAlgebra (π : A) (hπ : Irreducible π) :
    Algebra (rationalFunctionZeroDVR C) A :=
  (dvrUniformizerBaseMap C A π hπ).toRingHom.toAlgebra

/-- The original actual constants and the actual polynomial base form
an actual scalar tower, by the actual algebra homomorphism's commutation. -/
theorem dvrUniformizerBaseScalarTower (π : A) (hπ : Irreducible π) :
    letI : Algebra (rationalFunctionZeroDVR C) A := dvrUniformizerBaseAlgebra C A π hπ
    IsScalarTower C (rationalFunctionZeroDVR C) A := by
  letI : Algebra (rationalFunctionZeroDVR C) A := dvrUniformizerBaseAlgebra C A π hπ
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact ((dvrUniformizerBaseMap C A π hπ).commutes c).symm

/-- The actual domain module is torsion free under the proved injective
base map, hence flat over the genuine Dedekind polynomial DVR. -/
theorem dvrUniformizerBase_flat (π : A) (hπ : Irreducible π) :
    letI : Algebra (rationalFunctionZeroDVR C) A := dvrUniformizerBaseAlgebra C A π hπ
    Module.Flat (rationalFunctionZeroDVR C) A := by
  letI : Algebra (rationalFunctionZeroDVR C) A := dvrUniformizerBaseAlgebra C A π hπ
  letI : Module.IsTorsionFree (rationalFunctionZeroDVR C) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (dvrUniformizerBaseMap_injective C A π hπ)
  infer_instance

/-- Original essential finite type gives essential finite type over the
actual intermediate polynomial DVR; no converse from a fraction field is used. -/
theorem dvrUniformizerBase_essFiniteType [Algebra.EssFiniteType C A]
    (π : A) (hπ : Irreducible π) :
    letI : Algebra (rationalFunctionZeroDVR C) A := dvrUniformizerBaseAlgebra C A π hπ
    Algebra.EssFiniteType (rationalFunctionZeroDVR C) A := by
  letI : Algebra (rationalFunctionZeroDVR C) A := dvrUniformizerBaseAlgebra C A π hπ
  letI : IsScalarTower C (rationalFunctionZeroDVR C) A :=
    dvrUniformizerBaseScalarTower C A π hπ
  exact Algebra.EssFiniteType.of_comp C (rationalFunctionZeroDVR C) A

end ChenRanks
