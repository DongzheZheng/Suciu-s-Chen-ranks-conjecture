import ChenRanks.LogarithmicTwoFormResidue
import ChenRanks.DVRUnitOrder
import ChenRanks.LogarithmicRelations

/-!
# Actual ordered logarithmic mixed residues

The coefficient in the residue formula is the normalized order obtained
from the actual maximal-ideal valuation.  The source is the actual
logarithmic two-form lattice constructed in LogarithmicTwoFormResidue.
No residue detector or residue identity is an input hypothesis.

This local-ring result retains actual formal smoothness of A over C.
The differential in the other factor is an actual regular differential
on A; its restriction is the actual map to residue-field differentials.
The extension of geometric curve differentials to such regular forms
is a separate geometric step.
-/

noncomputable section

open scoped TensorProduct BigOperators

namespace ChenRanks

section ActualFiniteOrderProducts

variable (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]

/-- The actual normalized order of the multiplicative identity. -/
@[simp]
theorem localDVRUnitOrder_one : localDVRUnitOrder A F 1 = 0 := by
  simp only [localDVRUnitOrder, Units.val_one, map_one, WithZero.log_one, neg_zero]

/-- The actual valuation gives additive orders for genuine finite products. -/
theorem localDVRUnitOrder_prod {ι : Type*} (s : Finset ι) (f : ι → Fˣ) :
    localDVRUnitOrder A F (∏ i ∈ s, f i) = ∑ i ∈ s, localDVRUnitOrder A F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, localDVRUnitOrder_mul, Finset.sum_insert hi, ih]

/-- Genuine integral products have the genuine weighted valuation order. -/
theorem localDVRUnitOrder_prod_zpow {ι : Type*}
    (s : Finset ι) (f : ι → Fˣ) (n : ι → ℤ) :
    localDVRUnitOrder A F (∏ i ∈ s, f i ^ n i) =
      ∑ i ∈ s, n i * localDVRUnitOrder A F (f i) := by
  rw [localDVRUnitOrder_prod]
  simp only [localDVRUnitOrder_zpow]

end ActualFiniteOrderProducts

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

omit [CharZero C] [Algebra.EssFiniteType C A] [Algebra.FormallySmooth C A] in
/-- The actual two-form decomposition supplied by the actual ordered
uniformizer decomposition of the actual logarithmic differential. -/
theorem exists_logarithmicMixedTwoForm_order_decomposition
    (π : A) (hπ : Irreducible π) (f : Fˣ) (η : Ω[A⁄C]) :
    ∃ ω : Ω[A⁄C],
      exteriorWedge (k := F) (logarithmicDifferential C F f)
        (KaehlerDifferential.map C C A F η) =
      localDVRUnitOrder A F f • logarithmicMixedTwoFormMap C A F π hπ η +
        regularTwoFormMap C A F (ω ⊗ₜ[A] η) := by
  obtain ⟨ω, hω⟩ := exists_logarithmicDifferential_uniformizer_order_decomposition
    C A F π hπ f
  refine ⟨ω, ?_⟩
  rw [hω]
  change ((exteriorWedgeBilin (k := F) (E := Ω[F⁄C])).flip
    (KaehlerDifferential.map C C A F η))
    (localDVRUnitOrder A F f • logarithmicDifferential C F
      (LogResidueCore.fractionUniformizerUnit A F π hπ) +
        KaehlerDifferential.map C C A F ω) = _
  rw [map_add, map_zsmul]
  rfl

omit [CharZero C] [Algebra.EssFiniteType C A] [Algebra.FormallySmooth C A] in
/-- The actual logarithmic differential of any nonzero fraction, wedged
with an actual regular differential, belongs to the actual logarithmic lattice. -/
theorem fractionLogarithmicMixed_mem_lattice (π : A) (hπ : Irreducible π)
    (f : Fˣ) (η : Ω[A⁄C]) :
    exteriorWedge (k := F) (logarithmicDifferential C F f)
      (KaehlerDifferential.map C C A F η) ∈
      logarithmicTwoFormLattice C A F π hπ := by
  obtain ⟨ω, hω⟩ := exists_logarithmicMixedTwoForm_order_decomposition C A F π hπ f η
  rw [hω]
  have hn : localDVRUnitOrder A F f • logarithmicMixedTwoFormMap C A F π hπ η ∈
      logarithmicTwoFormLattice C A F π hπ := by
    simpa only [Int.cast_smul_eq_zsmul] using
      (logarithmicTwoFormLattice C A F π hπ).smul_mem (localDVRUnitOrder A F f : A)
        (logarithmicMixedTwoFormMap_mem_lattice C A F π hπ η)
  exact (logarithmicTwoFormLattice C A F π hπ).add_mem hn
    (regularTwoFormMap_mem_lattice C A F π hπ (ω ⊗ₜ[A] η))

/-- A genuine regular wedge as an element of the actual logarithmic lattice. -/
def regularWedgeInLogarithmicLattice (π : A) (hπ : Irreducible π)
    (ω η : Ω[A⁄C]) : logarithmicTwoFormLattice C A F π hπ :=
  ⟨regularTwoFormMap C A F (ω ⊗ₜ[A] η),
    regularTwoFormMap_mem_lattice C A F π hπ (ω ⊗ₜ[A] η)⟩

/-- A genuine uniformizer mixed form in the actual logarithmic lattice. -/
def uniformizerMixedInLogarithmicLattice (π : A) (hπ : Irreducible π)
    (η : Ω[A⁄C]) : logarithmicTwoFormLattice C A F π hπ :=
  ⟨logarithmicMixedTwoFormMap C A F π hπ η,
    logarithmicMixedTwoFormMap_mem_lattice C A F π hπ η⟩

/-- The actual mixed two-form associated to an actual nonzero fraction. -/
def fractionMixedInLogarithmicLattice (π : A) (hπ : Irreducible π)
    (f : Fˣ) (η : Ω[A⁄C]) : logarithmicTwoFormLattice C A F π hπ :=
  ⟨exteriorWedge (k := F) (logarithmicDifferential C F f)
    (KaehlerDifferential.map C C A F η),
      fractionLogarithmicMixed_mem_lattice C A F π hπ f η⟩

omit [CharZero C] [Algebra.EssFiniteType C A] [Algebra.FormallySmooth C A] in
@[simp]
theorem fractionMixedInLogarithmicLattice_coe (π : A) (hπ : Irreducible π)
    (f : Fˣ) (η : Ω[A⁄C]) :
    (fractionMixedInLogarithmicLattice C A F π hπ f η : ⋀[F]^2 Ω[F⁄C]) =
      exteriorWedge (k := F) (logarithmicDifferential C F f)
        (KaehlerDifferential.map C C A F η) := rfl

/-- The constructed actual residue has the actual normalized order as
coefficient.  This follows from the actual factorization and actual
regular/mixed residue identities. -/
theorem logarithmicTwoFormResidue_fractionMixed (π : A) (hπ : Irreducible π)
    (f : Fˣ) (η : Ω[A⁄C]) :
    logarithmicTwoFormResidue C A F π hπ
      (fractionMixedInLogarithmicLattice C A F π hπ f η) =
      localDVRUnitOrder A F f •
        KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) η := by
  obtain ⟨ω, hω⟩ := exists_logarithmicMixedTwoForm_order_decomposition C A F π hπ f η
  have hs : fractionMixedInLogarithmicLattice C A F π hπ f η =
      (localDVRUnitOrder A F f : A) • uniformizerMixedInLogarithmicLattice C A F π hπ η +
        regularWedgeInLogarithmicLattice C A F π hπ ω η := by
    apply Subtype.ext
    change exteriorWedge (k := F) (logarithmicDifferential C F f)
      (KaehlerDifferential.map C C A F η) =
      (localDVRUnitOrder A F f : A) • logarithmicMixedTwoFormMap C A F π hπ η +
        regularTwoFormMap C A F (ω ⊗ₜ[A] η)
    simpa only [Int.cast_smul_eq_zsmul] using hω
  rw [hs, map_add, map_smul]
  change (localDVRUnitOrder A F f : A) •
      logarithmicTwoFormResidue C A F π hπ
        ⟨logarithmicMixedTwoFormMap C A F π hπ η,
          logarithmicMixedTwoFormMap_mem_lattice C A F π hπ η⟩ +
      logarithmicTwoFormResidue C A F π hπ
        ⟨regularTwoFormMap C A F (ω ⊗ₜ[A] η),
          regularTwoFormMap_mem_lattice C A F π hπ (ω ⊗ₜ[A] η)⟩ = _
  rw [logarithmicTwoFormResidue_mixed, logarithmicTwoFormResidue_regular, add_zero]
  exact Int.cast_smul_eq_zsmul A (localDVRUnitOrder A F f) _

/-- The actual residue formula for an actual finite integral product,
with its coefficient computed from the actual valuations of its factors. -/
theorem logarithmicTwoFormResidue_fractionMixed_prod_zpow
    (π : A) (hπ : Irreducible π) {ι : Type*} (s : Finset ι)
    (f : ι → Fˣ) (n : ι → ℤ) (η : Ω[A⁄C]) :
    logarithmicTwoFormResidue C A F π hπ
      (fractionMixedInLogarithmicLattice C A F π hπ (∏ i ∈ s, f i ^ n i) η) =
      (∑ i ∈ s, n i * localDVRUnitOrder A F (f i)) •
        KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) η := by
  rw [logarithmicTwoFormResidue_fractionMixed, localDVRUnitOrder_prod_zpow]

/-- The same actual mixed form with the regular factor placed first. -/
def regularFractionMixedInLogarithmicLattice (π : A) (hπ : Irreducible π)
    (η : Ω[A⁄C]) (f : Fˣ) : logarithmicTwoFormLattice C A F π hπ :=
  (-1 : A) • fractionMixedInLogarithmicLattice C A F π hπ f η

omit [CharZero C] [Algebra.EssFiniteType C A] [Algebra.FormallySmooth C A] in
@[simp]
theorem regularFractionMixedInLogarithmicLattice_coe (π : A) (hπ : Irreducible π)
    (η : Ω[A⁄C]) (f : Fˣ) :
    (regularFractionMixedInLogarithmicLattice C A F π hπ η f : ⋀[F]^2 Ω[F⁄C]) =
      exteriorWedge (k := F) (KaehlerDifferential.map C C A F η)
        (logarithmicDifferential C F f) := by
  change (-1 : A) • exteriorWedge (k := F) (logarithmicDifferential C F f)
    (KaehlerDifferential.map C C A F η) = _
  rw [neg_one_smul]
  exact (wedge_swap (KaehlerDifferential.map C C A F η)
    (logarithmicDifferential C F f)).symm

/-- The actual reversed mixed residue carries the actual exterior sign. -/
theorem logarithmicTwoFormResidue_regularFractionMixed (π : A) (hπ : Irreducible π)
    (η : Ω[A⁄C]) (f : Fˣ) :
    logarithmicTwoFormResidue C A F π hπ
      (regularFractionMixedInLogarithmicLattice C A F π hπ η f) =
      -(localDVRUnitOrder A F f •
        KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) η) := by
  change logarithmicTwoFormResidue C A F π hπ
    ((-1 : A) • fractionMixedInLogarithmicLattice C A F π hπ f η) = _
  rw [map_smul, logarithmicTwoFormResidue_fractionMixed, neg_one_smul]

/-- A genuine finite relation between actual logarithmic mixed two-forms
implies the actual valuation-weighted relation in actual residue-field
differentials, by applying the constructed residue to the actual lattice. -/
theorem logarithmicMixed_relation_restricts_to_order_relation
    (π : A) (hπ : Irreducible π) {ι : Type*} (s : Finset ι)
    (a : ι → A) (f : ι → Fˣ) (η : ι → Ω[A⁄C])
    (h : ∑ i ∈ s, a i • exteriorWedge (k := F)
      (logarithmicDifferential C F (f i)) (KaehlerDifferential.map C C A F (η i)) = 0) :
    ∑ i ∈ s, a i • (localDVRUnitOrder A F (f i) •
      KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) (η i)) = 0 := by
  have hs : ∑ i ∈ s, a i • fractionMixedInLogarithmicLattice C A F π hπ (f i) (η i) = 0 := by
    apply Subtype.ext
    change (logarithmicTwoFormLattice C A F π hπ).subtype
      (∑ i ∈ s, a i • fractionMixedInLogarithmicLattice C A F π hπ (f i) (η i)) = 0
    simpa only [map_sum, map_smul, fractionMixedInLogarithmicLattice_coe] using h
  have hr := congrArg (logarithmicTwoFormResidue C A F π hπ) hs
  simpa only [map_sum, map_smul, map_zero, logarithmicTwoFormResidue_fractionMixed] using hr

/-- For actual constant coefficients, the constructed residue gives
an actual C-linear relation whose coefficients are the actual integer
orders, cast to C.  The source scalars are the actual images in A. -/
theorem logarithmicMixed_constant_relation_restricts_to_order_relation
    (π : A) (hπ : Irreducible π) {ι : Type*} (s : Finset ι)
    (c : ι → C) (f : ι → Fˣ) (η : ι → Ω[A⁄C])
    (h : ∑ i ∈ s, algebraMap C A (c i) • exteriorWedge (k := F)
      (logarithmicDifferential C F (f i)) (KaehlerDifferential.map C C A F (η i)) = 0) :
    ∑ i ∈ s, (c i * (localDVRUnitOrder A F (f i) : C)) •
      KaehlerDifferential.map C C A (IsLocalRing.ResidueField A) (η i) = 0 := by
  have hr := logarithmicMixed_relation_restricts_to_order_relation C A F π hπ s
    (fun i ↦ algebraMap C A (c i)) f η h
  simpa only [algebraMap_smul A, ← Int.cast_smul_eq_zsmul C, smul_smul] using hr

end ChenRanks
