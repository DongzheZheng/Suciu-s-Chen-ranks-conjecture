import ChenRanks.ArrangementEquationQuadraticCup
import ChenRanks.ArrangementMeridianClassIndependence
import ChenRanks.ResonanceObjects

/-!
# The actual first resonance of the original singular cohomology

The point set is defined directly from the actual native first cohomology
and its actual cup kernel. It exists before finite dimensionality or
equation-class spanning is proved. The original injective equation-class
map sends its actual coefficient resonance into this native point set.
Only containment is asserted: equality requires the separate spanning
theorem. No component count or Chen formula enters this definition.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open SingularCohomology Resonance

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

def singularResonance : Set A.singularH1 := Resonance.resonance A.singularCupKernel

theorem mem_singularResonance_iff {a : A.singularH1} (ha : a ≠ 0) :
    a ∈ A.singularResonance ↔
      ∃ b : A.singularH1, b ∉ ℂ ∙ a ∧ A.singularCup a b = 0 := by
  rw [singularResonance, Resonance.mem_resonance_iff A.singularCupKernel ha]
  constructor
  · rintro ⟨b, hba, hab⟩
    refine ⟨b, hba, ?_⟩
    change A.quadraticSingularCup (exteriorWedge a b) = 0 at hab
    rw [quadraticCup_exteriorWedge] at hab
    exact hab
  · rintro ⟨b, hba, hab⟩
    refine ⟨b, hba, ?_⟩
    change A.quadraticSingularCup (exteriorWedge a b) = 0
    rw [quadraticCup_exteriorWedge]
    exact hab

theorem equationWindingClassMap_mem_singularResonance
    (a : ι → ℂ) (ha : a ∈ Resonance.resonance A.equationQuadraticCupKernel) :
    A.equationWindingClassMap a ∈ A.singularResonance := by
  by_cases ha0 : a = 0
  · subst a
    rw [map_zero]
    exact Resonance.zero_mem_resonance A.singularCupKernel
  have hmapa : A.equationWindingClassMap a ≠ 0 := by
    intro h
    apply ha0
    apply A.equationWindingClassMap_injective
    simpa only [map_zero] using h
  obtain ⟨b, hba, hab⟩ :=
    (Resonance.mem_resonance_iff A.equationQuadraticCupKernel ha0).mp ha
  apply (A.mem_singularResonance_iff hmapa).mpr
  refine ⟨A.equationWindingClassMap b, ?_, ?_⟩
  · intro hline
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
    apply hba
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, A.equationWindingClassMap_injective ?_⟩
    rw [map_smul]
    exact hc
  · change A.equationQuadraticCup (exteriorWedge a b) = 0 at hab
    rw [A.equationQuadraticCup_exteriorWedge] at hab
    exact hab

end ChenRanks.AffineArrangement
