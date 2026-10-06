import ChenRanks.OrderedLogarithmicResidue

/-!
# Genuine mixed logarithmic relations with regular two-form remainders

The regular remainder is an element of the actual local differential
tensor product, mapped into the actual fraction-field exterior square.
The constructed logarithmic residue annihilates this actual remainder:
pure tensors follow from the proved regular-wedge formula, and the tensor
universal property gives the entire actual tensor module.

A vanishing relation consisting of actual logarithmic mixed terms and
such a genuine regular remainder therefore gives the genuine integer-order
weighted restriction relation. No residue detector, prescribed residue,
or regular-lift hypothesis is introduced.
-/

noncomputable section

open scoped TensorProduct BigOperators

namespace ChenRanks

variable (C A F : Type*) [Field C] [CharZero C] [CommRing A] [IsDomain A] [Field F]
  [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]
  [IsFractionRing A F] [IsDiscreteValuationRing A] [Algebra.EssFiniteType C A]
  [Algebra.FormallySmooth C A]

local instance : Module F (⋀[F]^2 Ω[F⁄C]) := exteriorTwoFormNativeFieldModule C F

local instance : SMul F (⋀[F]^2 Ω[F⁄C]) :=
  (exteriorTwoFormNativeFieldModule C F).toSMul

local instance : Module A (⋀[F]^2 Ω[F⁄C]) := exteriorTwoFormModuleRestriction C A F

local instance : SMul A (⋀[F]^2 Ω[F⁄C]) :=
  (exteriorTwoFormModuleRestriction C A F).toSMul

/-- The actual regular-tensor remainder as an element of the actual
logarithmic lattice. Membership follows from the actual regular map. -/
def regularTensorInLogarithmicLattice (π : A) (hπ : Irreducible π)
    (τ : Ω[A⁄C] ⊗[A] Ω[A⁄C]) : logarithmicTwoFormLattice C A F π hπ :=
  ⟨regularTwoFormMap C A F τ, regularTwoFormMap_mem_lattice C A F π hπ τ⟩

omit [CharZero C] [Algebra.EssFiniteType C A] [Algebra.FormallySmooth C A] in
@[simp]
theorem regularTensorInLogarithmicLattice_coe (π : A) (hπ : Irreducible π)
    (τ : Ω[A⁄C] ⊗[A] Ω[A⁄C]) :
    (regularTensorInLogarithmicLattice C A F π hπ τ : ⋀[F]^2 Ω[F⁄C]) =
      regularTwoFormMap C A F τ := rfl

/-- The constructed actual residue annihilates the whole genuine
regular-tensor image, not just a selected list of pure wedges. -/
theorem logarithmicTwoFormResidue_regularTensor (π : A) (hπ : Irreducible π)
    (τ : Ω[A⁄C] ⊗[A] Ω[A⁄C]) :
    logarithmicTwoFormResidue C A F π hπ
      (regularTensorInLogarithmicLattice C A F π hπ τ) = 0 := by
  let r : Ω[A⁄C] ⊗[A] Ω[A⁄C] →ₗ[A] logarithmicTwoFormLattice C A F π hπ :=
    (regularTwoFormMap C A F).codRestrict (logarithmicTwoFormLattice C A F π hπ)
      (regularTwoFormMap_mem_lattice C A F π hπ)
  have hzero : (logarithmicTwoFormResidue C A F π hπ).comp r = 0 := by
    apply TensorProduct.ext'
    intro ω η
    exact logarithmicTwoFormResidue_regular C A F π hπ ω η
  exact LinearMap.congr_fun hzero τ

/-- Applying the actual residue to a true mixed-plus-regular relation
gives its true valuation-weighted restriction relation. -/
theorem logarithmicMixed_regularTensor_relation_restricts_to_order_relation
    (π : A) (hπ : Irreducible π) {ι : Type*} (s : Finset ι)
    (a : ι → A) (f : ι → Fˣ) (η : ι → Ω[A⁄C])
    (τ : Ω[A⁄C] ⊗[A] Ω[A⁄C])
    (h : (∑ i ∈ s, a i • exteriorWedge (k := F)
      (logarithmicDifferential C F (f i)) (KaehlerDifferential.map C C A F (η i))) +
        regularTwoFormMap C A F τ = 0) :
    ∑ i ∈ s, a i • (localDVRUnitOrder A F (f i) •
      KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) (η i)) = 0 := by
  have hs : (∑ i ∈ s, a i • fractionMixedInLogarithmicLattice C A F π hπ (f i) (η i)) +
      regularTensorInLogarithmicLattice C A F π hπ τ = 0 := by
    apply Subtype.ext
    change (logarithmicTwoFormLattice C A F π hπ).subtype
      ((∑ i ∈ s, a i • fractionMixedInLogarithmicLattice C A F π hπ (f i) (η i)) +
        regularTensorInLogarithmicLattice C A F π hπ τ) = 0
    simpa only [map_add, map_sum, map_smul, fractionMixedInLogarithmicLattice_coe,
      regularTensorInLogarithmicLattice_coe] using h
  have hr := congrArg (logarithmicTwoFormResidue C A F π hπ) hs
  simpa only [map_add, map_sum, map_smul, map_zero,
    logarithmicTwoFormResidue_fractionMixed, logarithmicTwoFormResidue_regularTensor,
    add_zero] using hr

/-- Actual constant coefficients remain constant coefficients after
restriction, weighted by the true integer valuation orders. -/
theorem logarithmicMixed_regularTensor_constant_relation_restricts_to_order_relation
    (π : A) (hπ : Irreducible π) {ι : Type*} (s : Finset ι)
    (c : ι → C) (f : ι → Fˣ) (η : ι → Ω[A⁄C])
    (τ : Ω[A⁄C] ⊗[A] Ω[A⁄C])
    (h : (∑ i ∈ s, algebraMap C A (c i) • exteriorWedge (k := F)
      (logarithmicDifferential C F (f i)) (KaehlerDifferential.map C C A F (η i))) +
        regularTwoFormMap C A F τ = 0) :
    ∑ i ∈ s, (c i * (localDVRUnitOrder A F (f i) : C)) •
      KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) (η i) = 0 := by
  have hr := logarithmicMixed_regularTensor_relation_restricts_to_order_relation C A F
    π hπ s (fun i ↦ algebraMap C A (c i)) f η τ h
  simpa only [algebraMap_smul A, ← Int.cast_smul_eq_zsmul C, smul_smul] using hr

end ChenRanks
