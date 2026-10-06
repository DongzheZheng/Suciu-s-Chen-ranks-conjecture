import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Localization.Ideal

/-!
# Annihilators of genuine localizations of finite modules

The denominator common to a finite generating set is constructed in the
proof. Neither equality of annihilators nor a uniform denominator is an
input. This works for arbitrary commutative-ring localizations, including
localizations that are the zero ring.
-/

noncomputable section

namespace ChenRanks

variable (R : Type*) [CommRing R] (D : Submonoid R)
variable (A : Type*) [CommRing A] [Algebra R A] [hA : IsLocalization D A]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (N : Type*) [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] (f : M →ₗ[R] N) [hF : IsLocalizedModule D f]

include D f hA hF

/-- Every original annihilator acts by zero on the actual localized
module, by cancelling the genuine denominator of each module element. -/
theorem localizedModule_annihilator_map_le :
    (Module.annihilator R M).map (algebraMap R A) ≤ Module.annihilator A N := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change algebraMap R A r ∈ Module.annihilator A N
  rw [Module.mem_annihilator]
  intro n
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj D f n
  have hn : r • n = 0 := by
    apply IsLocalizedModule.smul_injective f s
    change (s : R) • (r • n) = (s : R) • (0 : N)
    have hs' : (s : R) • n = f m := hs
    rw [smul_comm, hs', ← f.map_smul,
      (Module.mem_annihilator.mp hr) m, f.map_zero, smul_zero]
  simpa only [algebraMap_smul] using hn

variable [Module.Finite R M]

/-- A scalar that annihilates the actual localization has a denominator
multiple annihilating every original generator and hence the whole
original finite module. -/
theorem localizedModule_annihilator_comap_le :
    (Module.annihilator A N).comap (algebraMap R A) ≤
      ((Module.annihilator R M).map (algebraMap R A)).comap (algebraMap R A) := by
  classical
  intro r hr
  change algebraMap R A r ∈ Module.annihilator A N at hr
  have hz : ∀ m : M, f (r • m) = 0 := by
    intro m
    rw [f.map_smul]
    have hm := (Module.mem_annihilator.mp hr) (f m)
    simpa only [algebraMap_smul] using hm
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  have hgens : ∀ m : (s : Set M), ∃ c : R, c ∈ D ∧ c • (r • (m : M)) = 0 := by
    intro m
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff D f).mp (hz m)
    exact ⟨c, c.property, hc⟩
  choose x hxD hx0 using hgens
  have hd : s.attach.prod x ∈ D := D.prod_mem (fun m _ ↦ hxD m)
  have hdann : s.attach.prod x * r ∈ Module.annihilator R M := by
    rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    intro m
    rw [mul_smul]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem x (Finset.mem_attach _ m)
    rw [hc, mul_comm, mul_smul, hx0, smul_zero]
  change algebraMap R A r ∈ (Module.annihilator R M).map (algebraMap R A)
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff D A
    (Module.annihilator R M) r).mpr ⟨s.attach.prod x, hd, hdann⟩

/-- The annihilator of a genuine localization of a finite module is
exactly the extension of its actual original annihilator. -/
theorem localizedModule_annihilator_eq_map :
    Module.annihilator A N = (Module.annihilator R M).map (algebraMap R A) := by
  apply le_antisymm
  · exact (IsLocalization.comap_le_comap_iff D A).mp
      (localizedModule_annihilator_comap_le R D A M N f)
  · exact localizedModule_annihilator_map_le R D A M N f

end ChenRanks
