import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.GroupTheory.Divisible
import Mathlib.Tactic.Abel

/-! A normalized symmetric additive two-cocycle with genuinely divisible
coefficients has a genuine primitive. Its central extension is constructed
with the actual cocycle as its group law, and native Baer extension gives
the splitting. This is a low-degree comparison tool, not an assumption of
group formality or of any higher Chen comparison.
-/

noncomputable section

namespace ChenRanks.GroupComparison

variable (A M : Type*) [AddCommGroup A] [AddCommGroup M]

/-- Actual normalized symmetric cocycle identities. These are explicit
intermediate data; an application must supply the actual cocycle and
prove these identities. -/
structure NormalizedSymmetricCocycle where
  toFun : A → A → M
  zero_right : ∀ a, toFun a 0 = 0
  symmetric : ∀ a b, toFun a b = toFun b a
  cocycle : ∀ a b d, toFun a b + toFun (a + b) d =
    toFun b d + toFun a (b + d)

variable {A M}

@[ext]
structure SymmetricCocycleExtension (c : NormalizedSymmetricCocycle A M) where
  central : M
  base : A

variable (c : NormalizedSymmetricCocycle A M)

instance extensionZero : Zero (SymmetricCocycleExtension c) := ⟨⟨0, 0⟩⟩

instance extensionAdd : Add (SymmetricCocycleExtension c) :=
  ⟨fun x y => ⟨x.central + y.central + c.toFun x.base y.base, x.base + y.base⟩⟩

instance extensionNeg : Neg (SymmetricCocycleExtension c) :=
  ⟨fun x => ⟨-x.central - c.toFun x.base (-x.base), -x.base⟩⟩

/-- The original central-extension operation is actually an abelian group. -/
instance extensionAddCommGroup : AddCommGroup (SymmetricCocycleExtension c) where
  add_assoc x y z := by
    apply SymmetricCocycleExtension.ext
    · change (x.central + y.central + c.toFun x.base y.base) + z.central +
        c.toFun (x.base + y.base) z.base =
        x.central + (y.central + z.central + c.toFun y.base z.base) +
          c.toFun x.base (y.base + z.base)
      calc
        _ = x.central + y.central + z.central +
            (c.toFun x.base y.base + c.toFun (x.base + y.base) z.base) := by abel
        _ = x.central + y.central + z.central +
            (c.toFun y.base z.base + c.toFun x.base (y.base + z.base)) := by
          rw [c.cocycle]
        _ = _ := by abel
    · exact add_assoc _ _ _
  zero_add x := by
    apply SymmetricCocycleExtension.ext
    · change 0 + x.central + c.toFun 0 x.base = x.central
      rw [c.symmetric, c.zero_right, zero_add, add_zero]
    · exact zero_add _
  add_zero x := by
    apply SymmetricCocycleExtension.ext
    · change x.central + 0 + c.toFun x.base 0 = x.central
      rw [c.zero_right, add_zero, add_zero]
    · exact add_zero _
  neg_add_cancel x := by
    apply SymmetricCocycleExtension.ext
    · change (-x.central - c.toFun x.base (-x.base)) + x.central +
        c.toFun (-x.base) x.base = 0
      rw [c.symmetric (-x.base) x.base]
      abel
    · exact neg_add_cancel _
  add_comm x y := by
    apply SymmetricCocycleExtension.ext
    · change x.central + y.central + c.toFun x.base y.base =
        y.central + x.central + c.toFun y.base x.base
      rw [c.symmetric x.base y.base, add_comm x.central y.central]
    · exact add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The actual coefficient group embeds in the actual extension. -/
def symmetricExtensionCentral : M →+ SymmetricCocycleExtension c where
  toFun m := ⟨m, 0⟩
  map_zero' := rfl
  map_add' m n := by
    apply SymmetricCocycleExtension.ext
    · change m + n = m + n + c.toFun 0 0
      rw [c.zero_right, add_zero]
    · exact (zero_add (0 : A)).symm

theorem symmetricExtensionCentral_injective :
    Function.Injective (symmetricExtensionCentral c) := by
  intro m n h
  exact congrArg SymmetricCocycleExtension.central h

/-- A genuine primitive derived from the actual central extension and
divisibility. No primitive or cohomology vanishing is an input. -/
theorem normalizedSymmetricCocycle_has_primitive [DivisibleBy M ℤ] :
    ∃ f : A → M, ∀ a b, f b - f (a + b) + f a = c.toFun a b := by
  obtain ⟨r, hr⟩ := (Module.Baer.of_divisible M).extension_property_addMonoidHom
    (symmetricExtensionCentral c) (symmetricExtensionCentral_injective c)
    (AddMonoidHom.id M)
  have hcentral (m : M) : r ⟨m, 0⟩ = m :=
    DFunLike.congr_fun hr m
  refine ⟨fun a => r ⟨0, a⟩, ?_⟩
  intro a b
  have hprod := r.map_add (⟨0, a⟩ : SymmetricCocycleExtension c) ⟨0, b⟩
  have hsplit := r.map_add
    (⟨c.toFun a b, 0⟩ : SymmetricCocycleExtension c) ⟨0, a + b⟩
  have heq : (⟨c.toFun a b, 0⟩ : SymmetricCocycleExtension c) + ⟨0, a + b⟩ =
      (⟨0, a⟩ : SymmetricCocycleExtension c) + ⟨0, b⟩ := by
    apply SymmetricCocycleExtension.ext
    · change c.toFun a b + 0 + c.toFun 0 (a + b) = 0 + 0 + c.toFun a b
      rw [c.symmetric 0 (a + b), c.zero_right]
      abel
    · exact zero_add _
  rw [heq] at hsplit
  rw [hcentral] at hsplit
  have h : r (⟨0, a⟩ : SymmetricCocycleExtension c) + r ⟨0, b⟩ =
      c.toFun a b + r ⟨0, a + b⟩ := hprod.symm.trans hsplit
  calc
    _ = (r (⟨0, a⟩ : SymmetricCocycleExtension c) + r ⟨0, b⟩) - r ⟨0, a + b⟩ :=
      by abel
    _ = c.toFun a b := (sub_eq_iff_eq_add).mpr h

end ChenRanks.GroupComparison
