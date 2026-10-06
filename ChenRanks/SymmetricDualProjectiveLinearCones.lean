import ChenRanks.SymmetricDualLinearPrimes
import ChenRanks.SymmetricDualProjectiveSupport
import ChenRanks.SymmetricDualNonzeroSpecialization
import Mathlib.Topology.Irreducible

/-!
# Actual generic points of original projective linear cones

The original cone ideal is the proved kernel of the genuine symmetric
restriction map, so it is truly prime and homogeneous. A genuine nonzero
original vector in `P` proves this same ideal relevant: containment of the
true irrelevant ideal would force the vector's genuine evaluation prime
to be the origin. Thus the ideal gives a native projective generic point.
The actual projective zero locus is its actual singleton closure, which
proves actual irreducibility.

Different actual separated maximal spaces give disjoint actual projective
cones. To check this at an arbitrary relevant prime, a genuine nonzero
evaluation specialization above that prime is constructed by the proved
Jacobson argument; the original dual equations recover membership in
both original subspaces. No projective closed-point classification or
disjointness detector is assumed.

These statements concern actual topological support, not reducedness.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

universe u

variable (k E : Type u) [Field k] [AddCommGroup E] [_root_.Module k E]
  [FiniteDimensional k E]
variable {ι : Type u} [Fintype ι]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

/-- A genuine nonzero original vector in the original subspace proves
the actual homogeneous cone ideal relevant. -/
theorem symmetricDualLinearHomogeneousIdeal_relevant
    (P : Submodule k E) {e : E} (heP : e ∈ P) (he : e ≠ 0) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousS k (_root_.Module.Dual k E) b) ≤
      symmetricDualLinearHomogeneousIdeal k E b P := by
  intro h
  have hOrigin : symmetricDualOriginIdeal k E ≤ symmetricDualLinearIdeal k E P := by
    rw [← homogeneousS_irrelevant_toIdeal_eq_origin k E b]
    exact h
  have hEval := (symmetricDualLinearIdeal_le_evaluationKernel_iff k E P e).mpr heP
  have hpunctured := (vectorEvaluationPrime_mem_punctured_iff k E e).mpr he
  change ¬ symmetricDualOriginIdeal k E ≤
    pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) at hpunctured
  exact hpunctured (hOrigin.trans hEval)

/-- The native projective generic point has exactly the same previously
defined original cone ideal, with actual relevance supplied by a true vector. -/
def symmetricDualLinearProjectiveGenericPoint
    (P : Submodule k E) {e : E} (heP : e ∈ P) (he : e ≠ 0) :
    ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b) where
  asHomogeneousIdeal := symmetricDualLinearHomogeneousIdeal k E b P
  isPrime := symmetricDualLinearIdeal_isPrime k E P
  not_irrelevant_le := symmetricDualLinearHomogeneousIdeal_relevant k E b P heP he

/-- The actual projective cone is the actual closure of its native
generic point, obtained from native projective vanishing-ideal topology. -/
theorem symmetricDualLinearProjectiveCone_eq_closure_genericPoint
    (P : Submodule k E) {e : E} (heP : e ∈ P) (he : e ≠ 0) :
    ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
        (symmetricDualLinearIdeal k E P : Set (S k (_root_.Module.Dual k E))) =
      closure ({symmetricDualLinearProjectiveGenericPoint k E b P heP he} :
        Set (ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b))) := by
  let p := symmetricDualLinearProjectiveGenericPoint k E b P heP he
  calc
    ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
        (symmetricDualLinearIdeal k E P : Set (S k (_root_.Module.Dual k E))) =
      ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
        (ProjectiveSpectrum.vanishingIdeal
          ({p} : Set (ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b))) :
            Set (S k (_root_.Module.Dual k E))) := by
      rw [ProjectiveSpectrum.vanishingIdeal_singleton]
      rfl
    _ = closure ({p} : Set (ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b))) :=
      ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _

/-- Every genuinely positive-dimensional original subspace has an
actual nonempty irreducible native projective linear cone. A nonzero
vector witness is constructed internally from its actual dimension. -/
theorem isIrreducible_symmetricDualLinearProjectiveCone
    (P : Submodule k E) (hdim : 0 < _root_.Module.finrank k P) :
    IsIrreducible (ProjectiveSpectrum.zeroLocus
      (homogeneousS k (_root_.Module.Dual k E) b)
        (symmetricDualLinearIdeal k E P : Set (S k (_root_.Module.Dual k E)))) := by
  letI : Nontrivial P := _root_.Module.nontrivial_of_finrank_pos hdim
  obtain ⟨e, he⟩ := exists_ne (0 : P)
  have heE : (e : E) ≠ 0 := by
    intro h
    apply he
    exact Subtype.ext h
  rw [symmetricDualLinearProjectiveCone_eq_closure_genericPoint k E b P e.property heE]
  exact isIrreducible_singleton.closure

section SeparatedIntersections

variable [IsAlgClosed k]

/-- At every actual native relevant prime, simultaneous membership in
two separated original maximal cones forces the two original spaces equal. -/
theorem maximal_isotropic_eq_of_common_projective_cone_prime
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)
    (P Q : OriginalMaximalIsotropicFamily (cupQuotient I))
    (q : ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b))
    (hqP : q ∈ ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
      (symmetricDualLinearIdeal k E P.val : Set (S k (_root_.Module.Dual k E))))
    (hqQ : q ∈ ProjectiveSpectrum.zeroLocus (homogeneousS k (_root_.Module.Dual k E) b)
      (symmetricDualLinearIdeal k E Q.val : Set (S k (_root_.Module.Dual k E)))) : P = Q := by
  obtain ⟨e, he, hqe⟩ :=
    symmetricDual_projectivePrime_exists_nonzero_evaluation_specialization k E b q
  have hPq : symmetricDualLinearIdeal k E P.val ≤ q.asHomogeneousIdeal.toIdeal := hqP
  have hQq : symmetricDualLinearIdeal k E Q.val ≤ q.asHomogeneousIdeal.toIdeal := hqQ
  have heP : e ∈ P.val :=
    (symmetricDualLinearIdeal_le_evaluationKernel_iff k E P.val e).mp (hPq.trans hqe)
  have heQ : e ∈ Q.val :=
    (symmetricDualLinearIdeal_le_evaluationKernel_iff k E Q.val e).mp (hQq.trans hqe)
  apply Subtype.ext
  apply maximalIsotropic_eq_of_nonzero_intersection_of_separated
    (cupQuotient I) P.val Q.val P.property.1 Q.property.1
  · simpa only [cupQuotient, Submodule.ker_mkQ] using hsep P.val P.property.1 P.property.2
  · exact heP
  · exact heQ
  · exact he

end SeparatedIntersections

end ChenRanks.Koszul
