import Mathlib
import ChenRanks.ConormalDifferentials
import ChenRanks.SmoothDifferentialLocalization

/-!
# A genuine normalized differential dual on a smooth DVR

The functional constructed here is obtained from the actual nonzero
uniformizer class in the actual conormal module, the proved conormal
retraction, and projectivity of the actual smooth Kähler module.  Its
normalization is proved.  No derivation or differential detector is
supplied as an input to the final construction.

The intermediate local-ring construction requires the genuine structural
condition `Algebra.FormallySmooth C A`.  Polynomial-chart localizations
derive that condition in `SmoothDifferentialLocalization`; a general
regular-local-ring smoothness theorem is not asserted here.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

section ActualUniformizerClass

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The actual uniformizer is a member of the actual maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (π : A) (hπ : Irreducible π) :
    π ∈ IsLocalRing.maximalIdeal A := by
  rw [hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton_self π

/-- The actual class of the actual uniformizer in `m/m²`. -/
def uniformizerCotangentVector (π : A) (hπ : Irreducible π) :
    IsLocalRing.CotangentSpace A :=
  (IsLocalRing.maximalIdeal A).toCotangent
    ⟨π, uniformizer_mem_maximalIdeal A π hπ⟩

/-- A uniformizer's actual conormal class is nonzero.  The proof uses
the actual DVR identity `m=(π)` and cancellation in the domain. -/
theorem uniformizerCotangentVector_ne_zero (π : A) (hπ : Irreducible π) :
    uniformizerCotangentVector A π hπ ≠ 0 := by
  intro h
  have hmem : π ∈ (IsLocalRing.maximalIdeal A) ^ 2 :=
    ((IsLocalRing.maximalIdeal A).toCotangent_eq_zero
      ⟨π, uniformizer_mem_maximalIdeal A π hπ⟩).mp h
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hunit : (1 : A) = π * a := by
    apply mul_left_cancel₀ hπ.ne_zero
    calc
      π * 1 = π := mul_one π
      _ = π ^ 2 * a := ha
      _ = π * (π * a) := by rw [pow_two, mul_assoc]
  exact hπ.not_isUnit (isUnit_of_dvd_one ⟨a, hunit⟩)

end ActualUniformizerClass

section ActualNormalizedLocalDual

variable (C A : Type*) [Field C] [CharZero C] [CommRing A] [IsDomain A]
  [Algebra C A] [IsDiscreteValuationRing A] [Algebra.EssFiniteType C A]

/-- A normalized residue-field-valued dual is constructed from the
proved actual conormal retraction and a dual of the actual uniformizer
class.  Its normalization is a conclusion. -/
theorem exists_localDifferentialDual_mod_uniformizer (π : A) (hπ : Irreducible π) :
    ∃ δ : Ω[A⁄C] →ₗ[A] IsLocalRing.ResidueField A,
      δ (KaehlerDifferential.D C A π) = 1 := by
  let κ := IsLocalRing.ResidueField A
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one κ
    (uniformizerCotangentVector_ne_zero A π hπ)
  obtain ⟨l, hl⟩ := exists_localConormal_retraction C A
  let t : Ω[A⁄C] →ₗ[A] κ ⊗[A] Ω[A⁄C] := TensorProduct.mk A κ Ω[A⁄C] 1
  refine ⟨(φ.restrictScalars A).comp (l.comp t), ?_⟩
  have hlπ : l ((1 : κ) ⊗ₜ[A] KaehlerDifferential.D C A π) =
      uniformizerCotangentVector A π hπ := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, localConormalMap,
      uniformizerCotangentVector, quotientConormalMap_toCotangent] using
      LinearMap.congr_fun hl (uniformizerCotangentVector A π hπ)
  change φ (l ((1 : κ) ⊗ₜ[A] KaehlerDifferential.D C A π)) = 1
  rw [hlπ]
  exact hφ

/-- Projectivity of the actual smooth Kähler module lifts the constructed
dual to the actual local ring.  Its value on `dπ` is a genuine local unit,
whose inverse normalizes the lift. -/
theorem exists_normalized_localDifferentialDual [Algebra.FormallySmooth C A]
    (π : A) (hπ : Irreducible π) :
    ∃ δ : Ω[A⁄C] →ₗ[A] A, δ (KaehlerDifferential.D C A π) = 1 := by
  obtain ⟨δκ, hδκ⟩ := exists_localDifferentialDual_mod_uniformizer C A π hπ
  let q : A →ₗ[A] IsLocalRing.ResidueField A := Algebra.linearMap A _
  obtain ⟨δ₀, hδ₀⟩ := Module.projective_lifting_property q δκ
    IsLocalRing.residue_surjective
  have he : IsLocalRing.residue A (δ₀ (KaehlerDifferential.D C A π)) = 1 := by
    exact (LinearMap.congr_fun hδ₀ (KaehlerDifferential.D C A π)).trans hδκ
  have hu : IsUnit (δ₀ (KaehlerDifferential.D C A π)) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [he]; exact one_ne_zero)
  obtain ⟨u, hu⟩ := hu
  refine ⟨((u⁻¹ : Aˣ) : A) • δ₀, ?_⟩
  simp only [LinearMap.smul_apply, smul_eq_mul, ← hu, Units.inv_mul]

/-- A genuine normalized local differential dual, selected only after
its existence and normalization have been proved. -/
def uniformizerLocalDifferentialDual [Algebra.FormallySmooth C A]
    (π : A) (hπ : Irreducible π) : Ω[A⁄C] →ₗ[A] A :=
  (exists_normalized_localDifferentialDual C A π hπ).choose

@[simp]
theorem uniformizerLocalDifferentialDual_D [Algebra.FormallySmooth C A]
    (π : A) (hπ : Irreducible π) :
    uniformizerLocalDifferentialDual C A π hπ (KaehlerDifferential.D C A π) = 1 :=
  (exists_normalized_localDifferentialDual C A π hπ).choose_spec

end ActualNormalizedLocalDual

section ActualFractionExtension

variable (C A F : Type*) [CommRing C] [CommRing A] [Field F]
  [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]
  [IsFractionRing A F]

/-- Extend an actual local Kähler dual to the actual fraction-field
Kähler module using the actual localization equivalence. -/
def fractionDifferentialDual (δ : Ω[A⁄C] →ₗ[A] A) : Ω[F⁄C] →ₗ[F] F := by
  letI : Algebra.FormallyEtale A F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact (((Algebra.linearMap A F).comp δ).liftBaseChange F).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale C A F).symm.toLinearMap

/-- The extended actual dual is regular on every actual regular form. -/
@[simp]
theorem fractionDifferentialDual_map (δ : Ω[A⁄C] →ₗ[A] A) (ω : Ω[A⁄C]) :
    fractionDifferentialDual C A F δ (KaehlerDifferential.map C C A F ω) =
      algebraMap A F (δ ω) := by
  letI : Algebra.FormallyEtale A F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have he : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale C A F).symm
      (KaehlerDifferential.map C C A F ω) = (1 : F) ⊗ₜ[A] ω := by
    apply (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale C A F).injective
    rw [LinearEquiv.apply_symm_apply]
    change KaehlerDifferential.map C C A F ω =
      KaehlerDifferential.mapBaseChange C A F ((1 : F) ⊗ₜ[A] ω)
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
  simp only [fractionDifferentialDual, LinearMap.comp_apply, LinearEquiv.coe_coe, he,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end ActualFractionExtension

section ActualNormalizedFractionDual

variable (C A F : Type*) [Field C] [CharZero C] [CommRing A] [IsDomain A] [Field F]
  [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]
  [IsFractionRing A F] [IsDiscreteValuationRing A] [Algebra.EssFiniteType C A]
  [Algebra.FormallySmooth C A]

/-- The constructed fraction-field dual used for actual logarithmic
contraction.  Its local source and normalization have been proved. -/
def uniformizerFractionDifferentialDual (π : A) (hπ : Irreducible π) : Ω[F⁄C] →ₗ[F] F :=
  fractionDifferentialDual C A F (uniformizerLocalDifferentialDual C A π hπ)

@[simp]
theorem uniformizerFractionDifferentialDual_map (π : A) (hπ : Irreducible π)
    (ω : Ω[A⁄C]) :
    uniformizerFractionDifferentialDual C A F π hπ (KaehlerDifferential.map C C A F ω) =
      algebraMap A F (uniformizerLocalDifferentialDual C A π hπ ω) :=
  fractionDifferentialDual_map C A F _ ω

/-- The actual extended dual sends the actual uniformizer differential
to one; no normalization hypothesis is introduced. -/
@[simp]
theorem uniformizerFractionDifferentialDual_D (π : A) (hπ : Irreducible π) :
    uniformizerFractionDifferentialDual C A F π hπ
      (KaehlerDifferential.D C F (algebraMap A F π)) = 1 := by
  rw [← KaehlerDifferential.map_D C C A F π, uniformizerFractionDifferentialDual_map,
    uniformizerLocalDifferentialDual_D, map_one]

end ActualNormalizedFractionDual

end ChenRanks
