import ChenRanks.KoszulResonanceSupport
import ChenRanks.KoszulOriginalModuleStructures
import ChenRanks.KoszulLocalizedTransverse
import ChenRanks.LocalizedTensorVanishing

/-!
# Literal original localization at a nonresonant nonzero point

The actual point-support theorem gives an element of the true original
annihilator outside the actual evaluation prime. This genuine
annihilating denominator kills the literal tensor localization. The
origin remains excluded, exactly as in the proved point-support
comparison; no local-zero, separation, or component-cover premise is
introduced.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]

local instance nonresonantOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def nonresonantOriginalCoefficientDictionary
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance nonresonantOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  nonresonantOriginalCoefficientDictionary k V K

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable [FiniteDimensional k E] [CharZero k]
variable (I : Submodule k (⋀[k]^2 E))

local instance (priority := 2000) nonresonantActualOriginalAddCommMonoid :
    AddCommMonoid (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (originalModuleAddCommGroup k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I)).toAddCommMonoid

local instance (priority := 2000) nonresonantActualOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
  (nonresonantOriginalCoefficientDictionary k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I)).toSMul

/-- The actual original Koszul localization vanishes at a genuine
nonzero point outside the actual resonance locus. -/
theorem originalKoszul_localization_eq_zero_of_nonresonant
    (e : E) (he : e ≠ 0) (hn : e ∉ ChenRanks.Resonance.resonance I)
    (z : PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
      ⊗[S k (_root_.Module.Dual k E)]
        Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) : z = 0 := by
  have hnot : ¬ _root_.Module.annihilator (S k (_root_.Module.Dual k E))
      (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) ≤
        pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e) := by
    intro h
    exact hn ((annihilator_point_iff_resonance k E I he).mp h)
  obtain ⟨s, hs, hsm⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ChenRanks.localizedTensor_eq_zero_of_annihilating_denominator
    (S k (_root_.Module.Dual k E))
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
    (pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e)).primeCompl
    (Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) s hsm
    (_root_.Module.mem_annihilator.mp hs) z

/-- The conclusion concerns the full native original tensor module. -/
theorem originalKoszul_localization_subsingleton_of_nonresonant
    (e : E) (he : e ≠ 0) (hn : e ∉ ChenRanks.Resonance.resonance I) :
    Subsingleton (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
      ⊗[S k (_root_.Module.Dual k E)]
        Module k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) := by
  refine ⟨fun z t => ?_⟩
  exact (originalKoszul_localization_eq_zero_of_nonresonant k E I e he hn z).trans
    (originalKoszul_localization_eq_zero_of_nonresonant k E I e he hn t).symm

end ChenRanks.Koszul
