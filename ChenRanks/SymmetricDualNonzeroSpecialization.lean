import ChenRanks.SymmetricDualProjectiveSupport

/-!
# Actual nonzero closed specializations of relevant symmetric primes

The true punctured cone intersected with the actual closure of a given
prime is a nonempty locally closed set: it contains that same prime.
The proved finite-type scalar morphism makes the actual symmetric cone
Jacobson. A genuine closed point in that locally closed set, followed by
the proved original-vector reconstruction, supplies an actual nonzero
evaluation prime containing the original prime. No maximal ideal,
nonzero specialization, or localization comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace ChenRanks.Koszul

universe u

variable (k E : Type u) [Field k] [IsAlgClosed k] [AddCommGroup E]
  [_root_.Module k E] [FiniteDimensional k E]

/-- Every actual punctured prime of the original symmetric algebra has
a true nonzero original-vector evaluation prime above it. -/
theorem symmetricDual_puncturedPrime_exists_nonzero_evaluation_specialization
    (q : PrimeSpectrum (S k (_root_.Module.Dual k E)))
    (hq : q ∈ symmetricDualPuncturedOpen k E) :
    ∃ e : E, e ≠ 0 ∧ q.asIdeal ≤
      pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) := by
  let X := Spec (CommRingCat.of (S k (_root_.Module.Dual k E)))
  let U : Set X := (symmetricDualPuncturedOpen k E :
    Set (PrimeSpectrum (S k (_root_.Module.Dual k E))))
  let Z : Set X := U ∩ PrimeSpectrum.zeroLocus (q.asIdeal : Set (S k (_root_.Module.Dual k E)))
  letI : JacobsonSpace X :=
    LocallyOfFiniteType.jacobsonSpace (symmetricDualScalarMorphism k E)
  have hZ : Z.Nonempty := ⟨q, hq, Set.Subset.rfl⟩
  have hZlocally : IsLocallyClosed Z :=
    (symmetricDualPuncturedOpen k E).isOpen.isLocallyClosed.inter
      (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed
  obtain ⟨m, hmZ, hmclosed⟩ := nonempty_inter_closedPoints hZ hZlocally
  obtain ⟨e, he, hem⟩ := symmetricDual_closedPuncturedPoint_exists_nonzero_vector
    k E m hmclosed hmZ.1
  refine ⟨e, he, ?_⟩
  have hqm : q.asIdeal ≤ m.asIdeal := hmZ.2
  rw [← hem] at hqm
  exact hqm

variable {ι : Type u} [Fintype ι]
  (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))

/-- The same true nonzero specialization exists above every actual
native relevant homogeneous prime, in the original affine symmetric ring. -/
theorem symmetricDual_projectivePrime_exists_nonzero_evaluation_specialization
    (q : ProjectiveSpectrum (homogeneousS k (_root_.Module.Dual k E) b)) :
    ∃ e : E, e ≠ 0 ∧ q.asHomogeneousIdeal.toIdeal ≤
      pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) :=
  symmetricDual_puncturedPrime_exists_nonzero_evaluation_specialization k E
    (symmetricDualProjectiveAffinePrime k E b q)
      (symmetricDualProjectiveAffinePrime_mem_punctured k E b q)

end ChenRanks.Koszul
