import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Genuine cardinal decrease after actual puncture exclusion

For an injective actual parametrization, its actual bad-point preimage
is finite. If its entire image excludes one actual member of the
original finite bad set, the true preimage cardinal is strictly smaller.
No cardinal decrease or finite detector is supplied as a premise.
-/

noncomputable section

namespace ChenRanks

theorem finitePuncturePreimage_ncard_lt {U V : Type*}
    (f : U → V) (hf : Function.Injective f)
    (S : Set V) (hS : S.Finite) (p : V) (hp : p ∈ S)
    (hexclude : ∀ q : U, f q ≠ p) :
    (f ⁻¹' S).Finite ∧ (f ⁻¹' S).ncard < S.ncard := by
  have hpre : (f ⁻¹' S).Finite := hS.preimage hf.injOn
  have himage : f '' (f ⁻¹' S) ⊂ S := by
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact hq
    · intro hback
      obtain ⟨q, _, hq⟩ := hback hp
      exact hexclude q hq
  have hc := Set.ncard_lt_ncard himage hS
  rw [Set.ncard_image_of_injective _ hf] at hc
  exact ⟨hpre, hc⟩

end ChenRanks
