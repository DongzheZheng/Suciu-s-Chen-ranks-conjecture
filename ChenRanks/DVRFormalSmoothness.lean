import ChenRanks.DVRUniformizerModel

/-!
# Formal smoothness of actual characteristic-zero finite-type DVRs

The actual polynomial DVR C[t]_(t), with t sent to an actual uniformizer
of A, is a formally smooth C-algebra.  Its actual map to A is local and
flat, and sends its actual maximal ideal onto the actual maximal ideal
of A.  Therefore its actual closed fiber is the actual residue field
of A, which is formally smooth over the actual characteristic-zero
residue field of the polynomial DVR.

The proved flat-and-smooth-closed-fiber criterion then gives formal
smoothness of A over that polynomial DVR, and composition gives formal
smoothness over C.  No regularity-to-smoothness axiom, flatness hypothesis,
residue detector, or smoothness hypothesis on A is introduced.
-/

noncomputable section

open IsLocalRing TensorProduct
open scoped Polynomial TensorProduct

namespace ChenRanks

section ActualClosedFiber

variable (R A : Type*) [CommRing R] [CommRing A]
  [IsLocalRing R] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]

/-- If the actual maximal-ideal image is the actual target maximal
ideal, the actual closed fiber is the actual residue field, with its
actual source-residue-field algebra structure. -/
def actualLocalClosedFiberResidueEquiv
    (h : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A) :
    ResidueField R ⊗[R] A ≃ₐ[ResidueField R] ResidueField A := by
  let e : ResidueField R ⊗[R] A ≃ₐ[R] A ⧸ (maximalIdeal R).map (algebraMap R A) :=
    (Algebra.TensorProduct.comm R (ResidueField R) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal R)).symm.restrictScalars R)
  exact AlgEquiv.extendScalarsOfSurjective residue_surjective
    (e.trans (Ideal.quotientEquivAlgOfEq R h))

/-- Formal smoothness transports along the actual closed-fiber
isomorphism.  This is a generic scalar-dictionary boundary; in the DVR
theorem the residue-field smoothness is derived from characteristic
zero and essential finite type. -/
theorem actualLocalClosedFiber_formallySmooth
    (h : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A)
    [Algebra.FormallySmooth (ResidueField R) (ResidueField A)] :
    Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] A) := by
  let e : ResidueField R ⊗[R] A ≃ₐ[ResidueField R] ResidueField A :=
    actualLocalClosedFiberResidueEquiv R A h
  exact Algebra.FormallySmooth.of_equiv
    (R := ResidueField R) (A := ResidueField A)
    (B := ResidueField R ⊗[R] A) e.symm

/-- The actual essential-finite-type localization witness supplies an
essential-finite-presentation witness over a Noetherian local base.
The algebra and scalar tower on the actual finite-type subalgebra are
cached explicitly, before applying the proved closed-fiber criterion. -/
theorem actualLocal_formallySmooth_of_flat_essFiniteType_smoothFiber
    [IsNoetherianRing R] [Module.Flat R A] [Algebra.EssFiniteType R A]
    [Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] A)] :
    Algebra.FormallySmooth R A := by
  let P : Subalgebra R A := Algebra.EssFiniteType.subalgebra R A
  letI : CommRing P := Subalgebra.toCommRing P
  letI : Algebra R P := Subalgebra.algebra P
  letI : Algebra P A := Subalgebra.toAlgebra P
  letI : IsScalarTower R P A := IsScalarTower.subalgebra' R A A P
  letI : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (R := R) (S := A) (P := P) (Algebra.EssFiniteType.submonoid R A)

end ActualClosedFiber

/-- The actual polynomial DVR is formally smooth over the actual
coefficient field, by actual polynomial smoothness and localization. -/
theorem rationalFunctionZeroDVR_formallySmooth (C : Type*) [Field C] :
    Algebra.FormallySmooth C (rationalFunctionZeroDVR C) := by
  letI : Algebra.FormallySmooth C[X] (rationalFunctionZeroDVR C) :=
    Algebra.FormallySmooth.of_isLocalization (polynomialZeroIdeal C).primeCompl
  exact Algebra.FormallySmooth.comp C C[X] (rationalFunctionZeroDVR C)

/-- An actual DVR essentially of finite type over a characteristic-zero
field is formally smooth.  All actual local/flat/fiber conditions used
by the criterion are proved from the actual uniformizer construction. -/
theorem dvr_formallySmooth_of_essFiniteType
    (C A : Type*) [Field C] [CharZero C] [CommRing A] [IsDomain A]
    [Algebra C A] [IsDiscreteValuationRing A] [Algebra.EssFiniteType C A] :
    Algebra.FormallySmooth C A := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let R := rationalFunctionZeroDVR C
  letI : Algebra R A := dvrUniformizerBaseAlgebra C A π hπ
  letI : IsScalarTower C R A := dvrUniformizerBaseScalarTower C A π hπ
  letI : IsLocalHom (algebraMap R A) := dvrUniformizerBaseMap_isLocalHom C A π hπ
  letI : Module.Flat R A := dvrUniformizerBase_flat C A π hπ
  letI : Algebra.EssFiniteType R A := dvrUniformizerBase_essFiniteType C A π hπ
  letI : Algebra.EssFiniteType C (ResidueField A) := by
    change Algebra.EssFiniteType C (A ⧸ maximalIdeal A)
    infer_instance
  letI : CharZero (ResidueField R) := Algebra.charZero_of_charZero C (ResidueField R)
  letI : Algebra.EssFiniteType (ResidueField R) (ResidueField A) :=
    Algebra.EssFiniteType.of_comp C (ResidueField R) (ResidueField A)
  letI : Algebra.FormallySmooth (ResidueField R) (ResidueField A) := inferInstance
  letI : Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] A) :=
    actualLocalClosedFiber_formallySmooth R A
      (dvrUniformizerBaseMap_maximalIdeal C A π hπ)
  letI : Algebra.FormallySmooth R A :=
    actualLocal_formallySmooth_of_flat_essFiniteType_smoothFiber R A
  letI : Algebra.FormallySmooth C R := rationalFunctionZeroDVR_formallySmooth C
  exact Algebra.FormallySmooth.comp C R A

end ChenRanks
