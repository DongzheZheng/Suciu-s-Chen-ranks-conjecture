import ChenRanks.LogarithmicOneFormResidue

/-!
# Actual constant coefficients detected by one-form residues

The actual one-form residue gives a relation in the actual residue field.
Its scalar embedding from the constant field is injective, so the same
integer-order relation already holds in the original constant field.
No characteristic-zero claim about a residue field is assumed separately.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable (C A F : Type*) [Field C] [CharZero C] [CommRing A] [IsDomain A] [Field F]
  [Algebra C A] [Algebra C F] [Algebra A F] [IsScalarTower C A F]
  [IsFractionRing A F] [IsDiscreteValuationRing A] [Algebra.EssFiniteType C A]
  [Algebra.FormallySmooth C A]

/-- Actual constant logarithmic coefficients satisfy the actual normalized
integer-order relation in the original constant field. -/
theorem logarithmicOneForm_constant_relation_orders {ι : Type*} (s : Finset ι)
    (π : A) (hπ : Irreducible π) (c : ι → C) (f : ι → Fˣ)
    (h : ∑ i ∈ s, algebraMap C A (c i) • logarithmicDifferential C F (f i) = 0) :
    ∑ i ∈ s, c i * (localDVRUnitOrder A F (f i) : C) = 0 := by
  have hr := logarithmicOneForm_relation_orders C A F s π hπ
    (fun i ↦ algebraMap C A (c i)) f h
  have hscalar : algebraMap C (IsLocalRing.ResidueField A)
      (∑ i ∈ s, c i * (localDVRUnitOrder A F (f i) : C)) = 0 := by
    simpa only [map_sum, map_mul, map_intCast,
      IsScalarTower.algebraMap_apply C A (IsLocalRing.ResidueField A), Algebra.smul_def] using hr
  exact (map_eq_zero_iff (algebraMap C (IsLocalRing.ResidueField A))
    (RingHom.injective _)).mp hscalar

end ChenRanks
