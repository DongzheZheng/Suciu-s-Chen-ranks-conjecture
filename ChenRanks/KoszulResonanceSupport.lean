import ChenRanks.KoszulPointAnnSupport
import ChenRanks.KoszulPointAomoto

/-!
# Genuine resonance and the original module's nonzero evaluation-point support

The module is the original Koszul first-cycle quotient on the actual dual
space, with the actual exterior annihilator of the given cup-product
kernel. All evaluation ideals and support points are genuine polynomial
evaluation kernels. The comparison is explicitly away from the origin.

Equality of point sets is not an equality of annihilator and minors
ideals, and does not assert projective scheme reducedness, effective
decomposition, arrangement cohomology, or the final Chen formula.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]

/-- The genuine prime-spectrum point given by the actual vector evaluation
ideal in the actual symmetric algebra on the dual space. -/
def vectorEvaluationPrime (e : E) : PrimeSpectrum (S k (_root_.Module.Dual k E)) :=
  ⟨pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e), inferInstance⟩

variable [FiniteDimensional k E] [CharZero k]

/-- The actual annihilator vanishes at an actual nonzero evaluation point
exactly when that vector lies in the genuine resonance point set. -/
theorem annihilator_point_iff_resonance
    (I : Submodule k (⋀[k]^2 E)) {e : E} (he : e ≠ 0) :
    _root_.Module.annihilator (S k (_root_.Module.Dual k E))
        (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) ≤
      pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) ↔
        e ∈ ChenRanks.Resonance.resonance I := by
  rw [← pointFibre_nontrivial_iff_annihilator_le k (_root_.Module.Dual k E)
    (pointOfVector k E e) (exteriorAnnihilator k E 2 I)]
  exact pointFibre_nontrivial_iff_resonance k E I he

/-- The actual polynomial-module support at the genuine evaluation prime
agrees with genuine resonance away from the origin. Actual module
finiteness is supplied by its proved finite-generation theorem. -/
theorem vectorEvaluationPrime_mem_support_iff_resonance
    (I : Submodule k (⋀[k]^2 E)) {e : E} (he : e ≠ 0) :
    vectorEvaluationPrime k E e ∈
        _root_.Module.support (S k (_root_.Module.Dual k E))
          (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) ↔
      e ∈ ChenRanks.Resonance.resonance I := by
  letI := actual_koszulModule_finite k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
  rw [_root_.Module.mem_support_iff_of_finite]
  exact annihilator_point_iff_resonance k E I he

/-- An explicit equality of genuine nonzero evaluation-point sets. The
origin is removed on both sides, with no hidden rank or component input. -/
theorem annihilator_nonzero_points_eq_resonance
    (I : Submodule k (⋀[k]^2 E)) :
    {e : E | e ≠ 0 ∧
      _root_.Module.annihilator (S k (_root_.Module.Dual k E))
          (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) ≤
        pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e)} =
      ChenRanks.Resonance.resonance I \ {0} := by
  ext e
  change (e ≠ 0 ∧ _) ↔ (e ∈ ChenRanks.Resonance.resonance I ∧ e ∉ ({0} : Set E))
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨(annihilator_point_iff_resonance k E I he).mp h, he⟩
  · rintro ⟨h, he⟩
    exact ⟨he, (annihilator_point_iff_resonance k E I he).mpr h⟩

end ChenRanks.Koszul
