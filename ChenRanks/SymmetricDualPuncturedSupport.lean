import ChenRanks.SymmetricDualClosedPoints
import ChenRanks.MaximalIsotropicFiniteFamily
import Mathlib.Topology.JacobsonSpace

/-!
# All actual punctured symmetric-cone support primes

The linear cones are defined by the actual symmetric generators belonging
to the original subspace's true dual annihilator. Their evaluation primes
are proved to detect membership in that original subspace by genuine
quotient-vector dual separation.

For the actual Koszul module attached to the actual quadratic cup kernel,
the already proved original annihilator/evaluation-fibre comparison is
used at actual nonzero closed points. The actual maximal-isotropic family
is finite by the proved separation theorem. The genuine finite-type
scalar morphism gives Jacobson density, which upgrades the closed-point
cover to an equality at every actual prime in the punctured symmetric
cone. Neither a finite cover nor an annihilator-support equality is input.

This is a topological support statement. It does not assert an equality
of ideals, reducedness, or a canonical decomposition of the module.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace ChenRanks.Koszul

open ChenRanks.Resonance

universe u

variable (k E : Type u) [Field k] [AddCommGroup E] [_root_.Module k E]

/-- The genuine homogeneous linear equations of the original subspace
inside the actual symmetric algebra on the original dual. -/
def symmetricDualLinearIdeal (P : Submodule k E) : Ideal (S k (_root_.Module.Dual k E)) :=
  Ideal.span (Set.range (fun φ : P.dualAnnihilator ↦
    SymmetricAlgebra.ι k (_root_.Module.Dual k E) φ.val))

/-- The original linear cone is its actual spectrum zero locus. -/
def symmetricDualLinearCone (P : Submodule k E) :
    Set (PrimeSpectrum (S k (_root_.Module.Dual k E))) :=
  PrimeSpectrum.zeroLocus (symmetricDualLinearIdeal k E P : Set (S k (_root_.Module.Dual k E)))

/-- Genuine duals of the original quotient detect precisely whether the
original vector lies in the original subspace. -/
theorem symmetricDualLinearIdeal_le_evaluationKernel_iff
    (P : Submodule k E) (e : E) :
    symmetricDualLinearIdeal k E P ≤
      pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) ↔ e ∈ P := by
  constructor
  · intro h
    by_contra hnot
    have hquot : P.mkQ e ≠ 0 := by
      intro hz
      exact hnot ((Submodule.Quotient.mk_eq_zero P).mp hz)
    obtain ⟨η, hη⟩ := _root_.Module.Projective.exists_dual_ne_zero k hquot
    let φ := η.comp P.mkQ
    have hφ : φ ∈ P.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro p hp
      change η (P.mkQ p) = 0
      have hz : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hp
      rw [hz]
      exact η.map_zero
    have hz := h (Ideal.subset_span (Set.mem_range_self
      (⟨φ, hφ⟩ : P.dualAnnihilator)))
    change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e)
      (SymmetricAlgebra.ι k (_root_.Module.Dual k E) φ) = 0 at hz
    simp only [pointEvaluation, SymmetricAlgebra.lift_ι_apply, pointOfVector,
      _root_.Module.Dual.eval_apply] at hz
    exact hη hz
  · intro he
    apply Ideal.span_le.mpr
    rintro s ⟨φ, rfl⟩
    change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e)
      (SymmetricAlgebra.ι k (_root_.Module.Dual k E) φ.val) = 0
    simp only [pointEvaluation, SymmetricAlgebra.lift_ι_apply, pointOfVector,
      _root_.Module.Dual.eval_apply]
    exact (Submodule.mem_dualAnnihilator (W := P) φ.val).mp φ.property e he

/-- Evaluation of the actual cone equations has the claimed original
vector meaning. -/
theorem vectorEvaluationPrime_mem_linearCone_iff (P : Submodule k E) (e : E) :
    vectorEvaluationPrime k E e ∈ symmetricDualLinearCone k E P ↔ e ∈ P :=
  symmetricDualLinearIdeal_le_evaluationKernel_iff k E P e

/-- The actual linear cone is closed at all prime points. -/
theorem isClosed_symmetricDualLinearCone (P : Submodule k E) :
    IsClosed (symmetricDualLinearCone k E P) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- The true annihilator of the original Koszul cycle quotient attached
to the original cup kernel. -/
abbrev symmetricDualActualAnnihilator (I : Submodule k (⋀[k]^2 E)) :
    Ideal (S k (_root_.Module.Dual k E)) :=
  _root_.Module.annihilator (S k (_root_.Module.Dual k E))
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I))

section AllPrimeSupport

variable [FiniteDimensional k E] [IsAlgClosed k] [CharZero k]

/-- Actual separation and the actual nonzero-point fibre theorem give
the support cover for all actual primes of the punctured symmetric cone.
The finite family and the passage from closed points to all primes are
constructed in the proof, rather than supplied as hypotheses. -/
theorem symmetricDual_punctured_annihilator_zeroLocus_eq
    (I : Submodule k (⋀[k]^2 E))
    (hsep : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P) :
    (symmetricDualPuncturedOpen k E :
      Set (PrimeSpectrum (S k (_root_.Module.Dual k E)))) ∩
        PrimeSpectrum.zeroLocus (symmetricDualActualAnnihilator k E I :
          Set (S k (_root_.Module.Dual k E))) =
      (symmetricDualPuncturedOpen k E :
        Set (PrimeSpectrum (S k (_root_.Module.Dual k E)))) ∩
        ⋃ P : OriginalMaximalIsotropicFamily (cupQuotient I),
          symmetricDualLinearCone k E P.val := by
  have hsep' : ∀ P : Submodule k E,
      IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
      2 ≤ _root_.Module.finrank k P →
      mixedExterior P ⊓ LinearMap.ker (cupQuotient I) = pureExterior P := by
    intro P hP hdim
    simpa only [cupQuotient, Submodule.ker_mkQ] using hsep P hP hdim
  letI := originalMaximalIsotropicFamilyFintype (cupQuotient I) hsep'
  let X := Spec (CommRingCat.of (S k (_root_.Module.Dual k E)))
  let U : Set X := (symmetricDualPuncturedOpen k E :
    Set (PrimeSpectrum (S k (_root_.Module.Dual k E))))
  let A : Set X := PrimeSpectrum.zeroLocus
    (symmetricDualActualAnnihilator k E I : Set (S k (_root_.Module.Dual k E)))
  let Z : Set X := ⋃ P : OriginalMaximalIsotropicFamily (cupQuotient I),
    symmetricDualLinearCone k E P.val
  have hAclosed : IsClosed A := PrimeSpectrum.isClosed_zeroLocus _
  have hZclosed : IsClosed Z := isClosed_iUnion_of_finite
    (fun P ↦ isClosed_symmetricDualLinearCone k E P.val)
  have hUopen : IsOpen U := (symmetricDualPuncturedOpen k E).isOpen
  letI : JacobsonSpace X :=
    LocallyOfFiniteType.jacobsonSpace (symmetricDualScalarMorphism k E)
  have hAZ : (U ∩ A) ∩ closedPoints X ⊆ Z := by
    rintro q ⟨⟨hqU, hqA⟩, hqclosed⟩
    obtain ⟨e, he, heq⟩ :=
      symmetricDual_closedPuncturedPoint_exists_nonzero_vector k E q hqclosed hqU
    have heA : symmetricDualActualAnnihilator k E I ≤
        pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) := by
      rw [← heq] at hqA
      exact hqA
    have heR := (annihilator_point_iff_resonance k E I he).mp heA
    obtain ⟨P, hP, hdim, heP⟩ := nonzero_resonance_mem_maximal_isotropic I he heR
    apply Set.mem_iUnion.mpr
    refine ⟨(⟨P, hP, hdim⟩ : OriginalMaximalIsotropicFamily (cupQuotient I)), ?_⟩
    rw [← heq]
    exact (vectorEvaluationPrime_mem_linearCone_iff k E P e).mpr heP
  have hZA : (U ∩ Z) ∩ closedPoints X ⊆ A := by
    rintro q ⟨⟨hqU, hqZ⟩, hqclosed⟩
    obtain ⟨e, he, heq⟩ :=
      symmetricDual_closedPuncturedPoint_exists_nonzero_vector k E q hqclosed hqU
    obtain ⟨P, hqP⟩ := Set.mem_iUnion.mp hqZ
    have heP : e ∈ P.val := by
      rw [← heq] at hqP
      exact (vectorEvaluationPrime_mem_linearCone_iff k E P.val e).mp hqP
    have heR : e ∈ resonance I :=
      (mem_resonance_iff_zero_or_mem_maximal_isotropic I e).mpr
        (Or.inr ⟨P.val, P.property.1, P.property.2, heP⟩)
    rw [← heq]
    exact (annihilator_point_iff_resonance k E I he).mpr heR
  have hAZall : U ∩ A ⊆ Z := by
    have hdensity := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (hUopen.isLocallyClosed.inter hAclosed.isLocallyClosed)
    have hclosure := hZclosed.closure_subset_iff.mpr hAZ
    rw [hdensity] at hclosure
    exact subset_closure.trans hclosure
  have hZAall : U ∩ Z ⊆ A := by
    have hdensity := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (hUopen.isLocallyClosed.inter hZclosed.isLocallyClosed)
    have hclosure := hAclosed.closure_subset_iff.mpr hZA
    rw [hdensity] at hclosure
    exact subset_closure.trans hclosure
  change U ∩ A = U ∩ Z
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨hq.1, hAZall hq⟩
  · intro q hq
    exact ⟨hq.1, hZAall hq⟩

end AllPrimeSupport

end ChenRanks.Koszul
