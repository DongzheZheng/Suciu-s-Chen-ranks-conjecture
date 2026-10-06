import ChenRanks.ArrangementSingularH1Spanning
import ChenRanks.ArrangementSingularResonance
import ChenRanks.ArrangementSingularCupKernelEquality

/-!
# Logarithmic coordinates for singular resonance

The equation-class equivalence identifies singular resonance witnesses
with logarithmic coefficients. Injectivity preserves linear independence,
and compatibility with the cup product preserves the quadratic relation.
Thus the singular resonance point set is the image of logarithmic
resonance under this equivalence.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open SingularCohomology Resonance

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

theorem equationWindingClassMap_mem_singularResonance_iff (a : ι → ℂ) :
    A.equationWindingClassMap a ∈ A.singularResonance ↔
      a ∈ resonance A.equationQuadraticCupKernel := by
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · subst a
      exact zero_mem_resonance A.equationQuadraticCupKernel
    have hmapa : A.equationWindingClassMap a ≠ 0 := by
      intro hz
      apply ha0
      apply A.equationWindingClassMap_injective
      simpa only [map_zero] using hz
    obtain ⟨b, hba, hab⟩ := (A.mem_singularResonance_iff hmapa).mp ha
    obtain ⟨c, rfl⟩ := A.equationWindingClassMap_surjective b
    apply (mem_resonance_iff A.equationQuadraticCupKernel ha0).mpr
    refine ⟨c, ?_, ?_⟩
    · intro hc
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hc
      apply hba
      apply Submodule.mem_span_singleton.mpr
      refine ⟨t, ?_⟩
      rw [← map_smul, ht]
    · change A.equationQuadraticCup (exteriorWedge a c) = 0
      rw [A.equationQuadraticCup_exteriorWedge]
      exact hab
  · exact A.equationWindingClassMap_mem_singularResonance a

theorem equationWindingClassMap_mem_singularResonance_iff_logarithmic (a : ι → ℂ) :
    A.equationWindingClassMap a ∈ A.singularResonance ↔
      a ∈ resonance A.rationalQuadraticKernel := by
  rw [A.equationWindingClassMap_mem_singularResonance_iff,
    A.equationQuadraticCupKernel_eq_rationalQuadraticKernel]

theorem singularResonance_eq_actual_equation_class_image :
    A.singularResonance = A.equationWindingClassMap '' resonance A.rationalQuadraticKernel := by
  ext h
  constructor
  · intro hh
    obtain ⟨a, rfl⟩ := A.equationWindingClassMap_surjective h
    exact ⟨a, (A.equationWindingClassMap_mem_singularResonance_iff_logarithmic a).mp hh, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (A.equationWindingClassMap_mem_singularResonance_iff_logarithmic a).mpr ha

end ChenRanks.AffineArrangement
