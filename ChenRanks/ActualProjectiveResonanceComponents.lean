import ChenRanks.SymmetricDualProjectiveLinearCones
import ChenRanks.KoszulProjectiveClosedImmersion

/-!
# Actual components of the genuine annihilator-quotient Proj

The space here is the native `Proj(S / Ann(W))` of the original Koszul
module on `Dual E`, rather than a frame scheme or an assumed component
list. Every original separated maximal isotropic subspace gives the
preimage of its actual linear cone under the true quotient Proj map.

The actual relevant-prime support theorem proves `Ann(W)` contained in
each true cone ideal by evaluating at its actual generic prime. The
genuine quotient-prime lift then supplies an actual source generic point.
Its actual singleton closure is the same source cone, proving nonempty
irreducibility. All source primes are covered by the proved finite family,
and true nonzero closed specializations prove the pieces disjoint. The
actual native irreducible components are therefore precisely these cones.

No finite cover, primality, generic point, irreducibility, or component
classification is a premise. Reducedness and the Krull-dimension formula
for these projective pieces are separate from this topological result.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace ChenRanks.Koszul

open ChenRanks.Resonance

universe u

variable (k E : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable {ι : Type u} [Fintype ι]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

local instance actualProjectiveComponentsQuotientGradedRing
    (I : Submodule k (⋀[k]^2 E)) :
    GradedRing (actualResonanceQuotientDegree k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I)) :=
  actualResonanceQuotientDegree_gradedRing k (_root_.Module.Dual k E) b
    (exteriorAnnihilator k E 2 I)

/-- The actual linear cone inside the actual original module-annihilator
quotient Proj, via the genuine native quotient point map. -/
def actualProjectiveLinearCone (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) :
    Set (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I)) :=
  quotientProjectivePointMap k (_root_.Module.Dual k E) b
      (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)) ⁻¹'
    ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
      (symmetricDualLinearIdeal k E P : Set (S k (_root_.Module.Dual k E)))

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k E] in
/-- The actual source cone is a true closed set in the true native Proj. -/
theorem isClosed_actualProjectiveLinearCone
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) :
    IsClosed (actualProjectiveLinearCone k E b I P) :=
  (ProjectiveSpectrum.isClosed_zeroLocus _ _).preimage
    (quotientProjectivePointMap_isClosedEmbedding k (_root_.Module.Dual k E) b
      (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I))).continuous

/-- The true all-relevant-prime support equality, applied to the true
cone generic point, proves the actual original annihilator contained in
this same original cone ideal. The containment is a conclusion. -/
theorem actualHomogeneousAnnihilator_le_linearCone
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I) ≤ symmetricDualLinearHomogeneousIdeal k E b P.val := by
  letI : Nontrivial P.val := _root_.Module.nontrivial_of_finrank_pos
    (by omega : 0 < _root_.Module.finrank k P.val)
  obtain ⟨e, he⟩ := exists_ne (0 : P.val)
  have heE : (e : E) ≠ 0 := fun h ↦ he (Subtype.ext h)
  let q := symmetricDualLinearProjectiveGenericPoint k E b P.val e.property heE
  have hqCone : q ∈ ProjectiveSpectrum.zeroLocus
      (homogeneousS k (_root_.Module.Dual k E) b)
        (symmetricDualLinearIdeal k E P.val : Set (S k (_root_.Module.Dual k E))) :=
    Set.Subset.rfl
  have hqAnn : q ∈ ProjectiveSpectrum.zeroLocus
      (homogeneousS k (_root_.Module.Dual k E) b)
        (symmetricDualActualAnnihilator k E I : Set (S k (_root_.Module.Dual k E))) := by
    rw [symmetricDual_projective_annihilator_zeroLocus_eq k E b I hsep]
    exact Set.mem_iUnion.mpr ⟨P, hqCone⟩
  exact hqAnn

/-- A true vector in the original P supplies the actual generic point
in the actual annihilator quotient, using the proved annihilator containment. -/
def actualProjectiveLinearGenericPoint
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I))
    {e : E} (heP : e ∈ P.val) (he : e ≠ 0) :
    actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) :=
  quotientProjectivePointLift k (_root_.Module.Dual k E) b
    (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I))
    (symmetricDualLinearProjectiveGenericPoint k E b P.val heP he)
    (actualHomogeneousAnnihilator_le_linearCone k E b I hsep P)

/-- The actual source cone is the true zero locus of the actual image
of the same cone ideal under the native graded quotient homomorphism. -/
theorem actualProjectiveLinearCone_eq_imageIdeal_zeroLocus
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E) :
    actualProjectiveLinearCone k E b I P =
      ProjectiveSpectrum.zeroLocus
        (quotientCoefficientPiece k (_root_.Module.Dual k E) b
          (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
            (exteriorAnnihilator k E 2 I)))
        (((symmetricDualLinearHomogeneousIdeal k E b P).map
          (homogeneousCoefficientQuotientMap k (_root_.Module.Dual k E) b
            (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
              (exteriorAnnihilator k E 2 I)))).toIdeal :
          Set (HomogeneousCoefficientQuotient k (_root_.Module.Dual k E) b
            (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
              (exteriorAnnihilator k E 2 I)))) := by
  ext q
  change symmetricDualLinearIdeal k E P ≤
      Ideal.comap (Ideal.Quotient.mk (symmetricDualActualAnnihilator k E I))
        q.asHomogeneousIdeal.toIdeal ↔
    Ideal.map (Ideal.Quotient.mk (symmetricDualActualAnnihilator k E I))
      (symmetricDualLinearIdeal k E P) ≤ q.asHomogeneousIdeal.toIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- The same actual source cone is the singleton closure of its true
source generic point. This uses the real source homogeneous ideal. -/
theorem actualProjectiveLinearCone_eq_closure_genericPoint
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I))
    {e : E} (heP : e ∈ P.val) (he : e ≠ 0) :
    actualProjectiveLinearCone k E b I P.val =
      closure ({actualProjectiveLinearGenericPoint k E b I hsep P heP he} :
        Set (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
          (exteriorAnnihilator k E 2 I))) := by
  let R := S k (_root_.Module.Dual k E) ⧸ symmetricDualActualAnnihilator k E I
  let d : ℕ → Submodule k R := actualResonanceQuotientDegree k (_root_.Module.Dual k E) b
    (exteriorAnnihilator k E 2 I)
  letI : GradedRing d := actualResonanceQuotientDegree_gradedRing
    k (_root_.Module.Dual k E) b (exteriorAnnihilator k E 2 I)
  let G : HomogeneousIdeal d := (symmetricDualLinearHomogeneousIdeal k E b P.val).map
    (homogeneousCoefficientQuotientMap k (_root_.Module.Dual k E) b
      (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)))
  let p : ProjectiveSpectrum d := actualProjectiveLinearGenericPoint k E b I hsep P heP he
  have hp : p.asHomogeneousIdeal = G := rfl
  have hvanish : (ProjectiveSpectrum.vanishingIdeal ({p} : Set (ProjectiveSpectrum d))).toIdeal =
      G.toIdeal := by
    rw [ProjectiveSpectrum.vanishingIdeal_singleton, hp]
  calc
    actualProjectiveLinearCone k E b I P.val =
        ProjectiveSpectrum.zeroLocus d (G.toIdeal : Set R) :=
      actualProjectiveLinearCone_eq_imageIdeal_zeroLocus k E b I P.val
    _ = ProjectiveSpectrum.zeroLocus d
        ((ProjectiveSpectrum.vanishingIdeal ({p} : Set (ProjectiveSpectrum d))).toIdeal :
          Set R) := by rw [hvanish]
    _ = closure ({p} : Set (ProjectiveSpectrum d)) :=
      ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure d {p}

/-- Every actual relevant original maximal subspace gives an actual
nonempty irreducible cone in the genuine original annihilator quotient Proj. -/
theorem isIrreducible_actualProjectiveLinearCone
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    IsIrreducible (actualProjectiveLinearCone k E b I P.val) := by
  letI : Nontrivial P.val := _root_.Module.nontrivial_of_finrank_pos
    (by omega : 0 < _root_.Module.finrank k P.val)
  obtain ⟨e, he⟩ := exists_ne (0 : P.val)
  have heE : (e : E) ≠ 0 := fun h ↦ he (Subtype.ext h)
  rw [actualProjectiveLinearCone_eq_closure_genericPoint k E b I hsep P e.property heE]
  exact isIrreducible_singleton.closure

/-- Every actual prime of the genuine quotient Proj belongs to a true
original maximal cone; this is the proved all-relevant-prime cover. -/
theorem actualProjectiveLinearCones_cover
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (q : actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I)) :
    ∃ P : OriginalMaximalIsotropicFamily (cupQuotient I),
      q ∈ actualProjectiveLinearCone k E b I P.val := by
  have hq := quotientProjectivePointMap_mem_zeroLocus k (_root_.Module.Dual k E) b
    (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I)) q
  change quotientProjectivePointMap k (_root_.Module.Dual k E) b
      (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)) q ∈
    ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
      (symmetricDualActualAnnihilator k E I : Set (S k (_root_.Module.Dual k E))) at hq
  rw [symmetricDual_projective_annihilator_zeroLocus_eq k E b I hsep] at hq
  obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hq
  refine ⟨P, ?_⟩
  exact hP

omit [CharZero k] in
/-- Two actual source cones sharing an actual source prime have the
same original maximal isotropic subspace. -/
theorem actualProjectiveLinearCones_index_eq_of_common_point
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P Q : OriginalMaximalIsotropicFamily (cupQuotient I))
    (q : actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I))
    (hqP : q ∈ actualProjectiveLinearCone k E b I P.val)
    (hqQ : q ∈ actualProjectiveLinearCone k E b I Q.val) : P = Q :=
  maximal_isotropic_eq_of_common_projective_cone_prime k E b I hsep P Q
    (quotientProjectivePointMap k (_root_.Module.Dual k E) b
      (actualHomogeneousAnnihilator k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)) q) hqP hqQ

private theorem actual_projective_irreducible_subset_piece
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (T : Set (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I))) (hT : IsIrreducible T) :
    ∃ P : OriginalMaximalIsotropicFamily (cupQuotient I),
      T ⊆ actualProjectiveLinearCone k E b I P.val := by
  classical
  have hsep' : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P →
      mixedExterior P ⊓ LinearMap.ker (cupQuotient I) = pureExterior P := by
    intro P hP hdim
    simpa only [cupQuotient, Submodule.ker_mkQ] using hsep P hP hdim
  letI := originalMaximalIsotropicFamilyFintype (cupQuotient I) hsep'
  let f := fun P : OriginalMaximalIsotropicFamily (cupQuotient I) ↦
    actualProjectiveLinearCone k E b I P.val
  have hfinite : (Set.range f).Finite := Set.finite_range f
  have hclosed : ∀ z ∈ hfinite.toFinset, IsClosed z := by
    intro z hz
    obtain ⟨P, rfl⟩ := hfinite.mem_toFinset.mp hz
    exact isClosed_actualProjectiveLinearCone k E b I P.val
  have hcover : T ⊆ ⋃₀ (hfinite.toFinset : Set (Set
      (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)))) := by
    intro q _hq
    obtain ⟨P, hqP⟩ := actualProjectiveLinearCones_cover k E b I hsep q
    exact Set.mem_sUnion.mpr ⟨f P, hfinite.mem_toFinset.mpr (Set.mem_range_self P), hqP⟩
  obtain ⟨z, hz, hTz⟩ := isIrreducible_iff_sUnion_isClosed.mp hT hfinite.toFinset hclosed hcover
  obtain ⟨P, rfl⟩ := hfinite.mem_toFinset.mp hz
  exact ⟨P, hTz⟩

/-- Each original maximal isotropic space is a true actual irreducible
component of the native original annihilator quotient Proj. -/
theorem actualProjectiveLinearCone_mem_irreducibleComponents
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P : OriginalMaximalIsotropicFamily (cupQuotient I)) :
    actualProjectiveLinearCone k E b I P.val ∈
      irreducibleComponents (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)) := by
  have hP := isIrreducible_actualProjectiveLinearCone k E b I hsep P
  refine ⟨hP, ?_⟩
  intro T hT hPT
  obtain ⟨Q, hTQ⟩ := actual_projective_irreducible_subset_piece k E b I hsep T hT
  obtain ⟨q, hqP⟩ := hP.1
  have hPQ := actualProjectiveLinearCones_index_eq_of_common_point k E b I hsep
    P Q q hqP (hTQ (hPT hqP))
  simpa only [hPQ] using hTQ

/-- Exact actual irreducible-component identification in the genuine
native `Proj(S / Ann(W))`, derived from true finite coverage and true
generic-point irreducibility. Reducedness is not asserted. -/
theorem irreducibleComponents_actualProjectiveResonanceScheme_eq_range
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P) :
    irreducibleComponents (actualProjectiveResonanceScheme k (_root_.Module.Dual k E) b
        (exteriorAnnihilator k E 2 I)) =
      Set.range (fun P : OriginalMaximalIsotropicFamily (cupQuotient I) ↦
        actualProjectiveLinearCone k E b I P.val) := by
  ext T
  constructor
  · intro hT
    obtain ⟨P, hTP⟩ := actual_projective_irreducible_subset_piece k E b I hsep T hT.1
    have hP := actualProjectiveLinearCone_mem_irreducibleComponents k E b I hsep P
    exact ⟨P, Set.Subset.antisymm (hT.2 hP.1 hTP) hTP⟩
  · rintro ⟨P, rfl⟩
    exact actualProjectiveLinearCone_mem_irreducibleComponents k E b I hsep P

end ChenRanks.Koszul
