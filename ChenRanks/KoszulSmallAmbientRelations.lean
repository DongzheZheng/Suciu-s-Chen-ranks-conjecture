import ChenRanks.KoszulFullRelations
import ChenRanks.KoszulComponentDuality
import ChenRanks.MaximalIsotropicFiniteFamily
import ChenRanks.ResonanceObjects
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# True quadratic-relation and component boundaries in dimension at most two

The actual exterior square has dimension at most one, so its genuine
quadratic submodules are zero or the whole exterior square. The zero
cup kernel has no actual maximal isotropic component of dimension at
least two; for the full cup kernel every actual maximal isotropic
subspace is the whole ambient space. These statements use the original
exterior map and original maximal-isotropic subtype. They do not assert
a general effective bound, a graded canonical-map isomorphism or a Chen
comparison.
-/

noncomputable section

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]

/-- A genuine quadratic kernel in ambient dimension at most two has
only the zero and full possibilities. -/
theorem quadraticSubmodule_eq_bot_or_top_of_finrank_le_two
    (I : Submodule k (⋀[k]^2 E)) (hE : _root_.Module.finrank k E ≤ 2) :
    I = ⊥ ∨ I = ⊤ := by
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    have hdim : _root_.Module.finrank k (⋀[k]^2 E) ≤ 1 := by
      rcases (show _root_.Module.finrank k E = 0 ∨
          _root_.Module.finrank k E = 1 ∨ _root_.Module.finrank k E = 2 by omega)
        with h | h | h <;> rw [exteriorPower.finrank_eq, h] <;> decide
    have hpositive : 0 < _root_.Module.finrank k I :=
      (_root_.Module.finrank_pos_iff_of_free k I).mpr
        (Submodule.nontrivial_iff_ne_bot.mpr hI)
    have hle := I.finrank_le
    apply Submodule.eq_top_of_finrank_eq
    omega

/-- Actual isotropy for a zero cup kernel forces dimension at most one,
by injectivity of the genuine exterior inclusion. -/
theorem zeroCupKernel_isotropic_finrank_le_one (P : Submodule k E)
    (hP : IsIsotropic (relationWedge (cupQuotient (⊥ : Submodule k (⋀[k]^2 E)))) P) :
    _root_.Module.finrank k P ≤ 1 := by
  have hpure : pureExterior P ≤ (⊥ : Submodule k (⋀[k]^2 E)) :=
    (isCupIsotropic_iff_isIsotropic (⊥ : Submodule k (⋀[k]^2 E)) P).mpr hP
  have hmap : exteriorPower.map 2 P.subtype = 0 :=
    LinearMap.range_eq_bot.mp (bot_unique hpure)
  have hinj : Function.Injective (exteriorPower.map 2 P.subtype) :=
    exteriorPower.map_injective_field P.subtype_injective
  letI : Subsingleton (⋀[k]^2 P) := ⟨fun x y => hinj (by
    rw [hmap, LinearMap.zero_apply, LinearMap.zero_apply])⟩
  have hzero : _root_.Module.finrank k (⋀[k]^2 P) = 0 :=
    _root_.Module.finrank_eq_zero_of_subsingleton k _
  rw [exteriorPower.finrank_eq] at hzero
  have hlt := Nat.choose_eq_zero_iff.mp hzero
  omega

/-- The literal original component subtype is empty for zero cup kernel. -/
theorem zeroCupKernel_originalFamily_isEmpty :
    IsEmpty (OriginalMaximalIsotropicFamily (cupQuotient (⊥ : Submodule k (⋀[k]^2 E)))) := by
  constructor
  intro P
  have hle := zeroCupKernel_isotropic_finrank_le_one k E P.val P.property.1.1
  have hge := P.property.2
  omega

/-- Every original maximal isotropic space for a full cup kernel is
really the entire original ambient space. -/
theorem fullCupKernel_maximal_isotropic_eq_top (P : Submodule k E)
    (hP : IsMaximalIsotropic
      (relationWedge (cupQuotient (⊤ : Submodule k (⋀[k]^2 E)))) P) : P = ⊤ := by
  have htop : IsIsotropic
      (relationWedge (cupQuotient (⊤ : Submodule k (⋀[k]^2 E)))) ⊤ :=
    (isCupIsotropic_iff_isIsotropic (⊤ : Submodule k (⋀[k]^2 E)) ⊤).mp le_top
  exact le_antisymm le_top (hP.2 ⊤ le_top htop)

/-- The actual determinant-pairing annihilator of zero is full. -/
theorem exteriorAnnihilator_bot (n : ℕ) :
    exteriorAnnihilator k E n (⊥ : Submodule k (⋀[k]^n E)) = ⊤ := by
  unfold exteriorAnnihilator
  rw [Submodule.dualAnnihilator_bot, Submodule.comap_top]

end ChenRanks.Koszul
