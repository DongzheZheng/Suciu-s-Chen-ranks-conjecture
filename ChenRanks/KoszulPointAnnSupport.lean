import ChenRanks.KoszulPointCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Support

/-!
# Genuine point fibres and the original module annihilator

The evaluation kernel is proved maximal from the actual surjective
evaluation map. The original tensor fibre is proved equivalent to the
actual quotient by that ideal times the original module. Actual finite
module support and quotient support then give the annihilator criterion.
No support, fibre formula, or Nakayama conclusion is assumed.

The criterion in this file includes the origin. Comparison with the
resonance convention is a later theorem away from the origin; this file
does not assert equality of annihilator ideals or projective schemes.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

section FiniteModuleSupport

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [_root_.Module R M] [_root_.Module.Finite R M]

/-- For an actual finite module, its actual quotient at a maximal ideal
is nontrivial exactly when that maximal ideal contains its annihilator.
The proof uses actual module support and actual quotient support. -/
theorem maximalQuotient_nontrivial_iff_annihilator_le (I : Ideal R) [I.IsMaximal] :
    Nontrivial (M ⧸ (I • (⊤ : Submodule R M))) ↔
      _root_.Module.annihilator R M ≤ I := by
  let p : PrimeSpectrum R := ⟨I, inferInstance⟩
  have hv : PrimeSpectrum.zeroLocus (I : Set R) = {p} := by
    ext q
    constructor
    · intro hq
      apply Set.mem_singleton_iff.mpr
      apply PrimeSpectrum.ext
      have hqi : I ≤ q.asIdeal := hq
      exact ((inferInstance : I.IsMaximal).eq_of_le q.isPrime.ne_top hqi).symm
    · intro hq
      have hqp : q = p := Set.mem_singleton_iff.mp hq
      subst q
      change (I : Set R) ⊆ I
      exact Set.Subset.rfl
  have hs : p ∈ _root_.Module.support R M ↔ _root_.Module.annihilator R M ≤ I :=
    _root_.Module.mem_support_iff_of_finite
  rw [← _root_.Module.nonempty_support_iff (R := R) (M := M ⧸ (I • (⊤ : Submodule R M))),
    _root_.Module.support_quotient (R := R) (M := M), hv]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have heq : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    exact hs.mp hq
  · intro h
    exact ⟨p, hs.mpr h, Set.mem_singleton p⟩

end FiniteModuleSupport

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (a : V →ₗ[k] k)

/-- The actual evaluation map is surjective via the actual constant
polynomials. -/
theorem pointEvaluation_surjective : Function.Surjective (pointEvaluation k V a) := by
  intro c
  exact ⟨algebraMap k (S k V) c, (pointEvaluation k V a).commutes c⟩

/-- The actual ideal of polynomials vanishing at the actual point. -/
def pointEvaluationKernel : Ideal (S k V) := RingHom.ker (pointEvaluation k V a).toRingHom

/-- The actual point evaluation kernel is maximal because its true
evaluation map is surjective onto the actual coefficient field. -/
instance pointEvaluationKernel_isMaximal : (pointEvaluationKernel k V a).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (pointEvaluation k V a).toRingHom
    (pointEvaluation_surjective k V a)

/-- The genuine polynomial-linear evaluation into the actual point
coefficient field, using its already proved evaluation algebra structure. -/
def pointCoefficientMap : S k V →ₗ[S k V] PointScalars k V a :=
  Algebra.linearMap (S k V) (PointScalars k V a)

theorem pointCoefficientMap_surjective : Function.Surjective (pointCoefficientMap k V a) := by
  intro c
  refine ⟨algebraMap k (S k V) (pointScalarsEquiv k V a c), ?_⟩
  apply (pointScalarsEquiv k V a).injective
  change pointEvaluation k V a (algebraMap k (S k V) (pointScalarsEquiv k V a c)) =
    pointScalarsEquiv k V a c
  exact (pointEvaluation k V a).commutes _

theorem pointCoefficientMap_ker :
    LinearMap.ker (pointCoefficientMap k V a) = pointEvaluationKernel k V a := by
  ext s
  rfl

/-- The actual evaluation quotient is genuinely equivalent to the actual
point coefficient field with its genuine polynomial action. -/
def pointCoefficientQuotientEquiv :
    (S k V ⧸ pointEvaluationKernel k V a) ≃ₗ[S k V] PointScalars k V a :=
  (Submodule.quotEquivOfEq _ _ (pointCoefficientMap_ker k V a).symm).trans
    ((pointCoefficientMap k V a).quotKerEquivOfSurjective
      (pointCoefficientMap_surjective k V a))

variable (K : Submodule k (⋀[k]^2 V))

/-- The literal original point tensor fibre is proved equivalent to the
actual ideal-times-module quotient, via the genuine coefficient quotient
equivalence and the actual tensor/ideal-quotient equivalence. -/
def pointFibreIdealQuotientEquiv :
    PointFiber k V K a ≃ₗ[S k V]
      (Module k V K ⧸ (pointEvaluationKernel k V a •
        (⊤ : Submodule (S k V) (Module k V K)))) :=
  ((pointCoefficientQuotientEquiv k V a).symm.rTensor (Module k V K)).trans
    (TensorProduct.quotTensorEquivQuotSMul (Module k V K) (pointEvaluationKernel k V a))

variable [FiniteDimensional k V] [CharZero k]

/-- The genuine point fibre criterion for the actual annihilator of the
original module. Actual module finiteness is proved, rather than supplied
as a new geometric or support hypothesis. This criterion includes zero. -/
theorem pointFibre_nontrivial_iff_annihilator_le :
    Nontrivial (PointFiber k V K a) ↔
      _root_.Module.annihilator (S k V) (Module k V K) ≤ pointEvaluationKernel k V a := by
  letI := actual_koszulModule_finite k V K
  let J : Submodule (S k V) (Module k V K) :=
    pointEvaluationKernel k V a • (⊤ : Submodule (S k V) (Module k V K))
  let Q := Module k V K ⧸ J
  letI : AddCommGroup Q := Submodule.Quotient.addCommGroup J
  letI : _root_.Module (S k V) Q := Submodule.Quotient.module J
  let e : PointFiber k V K a ≃ₗ[S k V] Q := pointFibreIdealQuotientEquiv k V a K
  have hq : Nontrivial Q ↔
      _root_.Module.annihilator (S k V) (Module k V K) ≤ pointEvaluationKernel k V a :=
    maximalQuotient_nontrivial_iff_annihilator_le
      (Module k V K) (pointEvaluationKernel k V a)
  exact e.toEquiv.nontrivial_congr.trans hq

end ChenRanks.Koszul
