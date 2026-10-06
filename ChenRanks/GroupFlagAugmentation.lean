import ChenRanks.DegreeRaisingEndomorphisms
import ChenRanks.GroupAlgebraAugmentationSpan
import ChenRanks.GroupLowerCentralAugmentation
import ChenRanks.ScalarLowerCentralPieceBracket

/-!
# Actual original group-ring augmentation in the actual operator flag

The representation is an actual monoid homomorphism of the original
group to units of its native endomorphism ring. The native group-algebra
universal map is applied to the original augmentation ideal and its
actual powers. Degree-one deviation is an intermediate structural
condition on this actual representation; the final positive monodromy
must derive it from its constructed flag. No dimension-subgroup equality
or injectivity of the original lower-central quotients is assumed.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct commutatorElement

namespace ChenRanks.LieComparison

variable (k G E : Type*) [Field k] [Group G] [AddCommGroup E] [Module k E]
variable (F : ℕ → Submodule k E)

/-- The actual native group-algebra universal homomorphism. -/
def flagRepresentationAlgebra (ρ : G →* (Module.End k E)ˣ) :
    MonoidAlgebra k G →ₐ[k] Module.End k E :=
  MonoidAlgebra.lift k (Module.End k E) G
    ((Units.coeHom (Module.End k E)).comp ρ)

@[simp] theorem flagRepresentationAlgebra_of
    (ρ : G →* (Module.End k E)ˣ) (g : G) :
    flagRepresentationAlgebra k G E ρ (MonoidAlgebra.of k G g) =
      (ρ g : Module.End k E) :=
  MonoidAlgebra.lift_of _ g

@[simp] theorem flagRepresentationAlgebra_difference
    (ρ : G →* (Module.End k E)ˣ) (g : G) :
    flagRepresentationAlgebra k G E ρ
      (GroupAlgebra.augmentationDifference k G g) = (ρ g : Module.End k E) - 1 := by
  rw [GroupAlgebra.augmentationDifference, map_sub,
    flagRepresentationAlgebra_of, map_one]

/-- Every original group element preserves the flag because its actual
deviation raises it by one and the actual flag is antitone. -/
theorem flagRepresentation_mem_degree_zero
    (hF : Antitone F) (ρ : G →* (Module.End k E)ˣ)
    (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
      degreeRaisingEndomorphisms k E F 1) (g : G) :
    (ρ g : Module.End k E) ∈ degreeRaisingEndomorphisms k E F 0 := by
  have hdev := degreeRaisingEndomorphisms_antitone k E F hF 0 1
    (Nat.zero_le 1) (hρ g)
  have hsum := (degreeRaisingEndomorphisms k E F 0).add_mem hdev
    (one_mem_degreeRaisingEndomorphisms k E F)
  simpa only [sub_add_cancel] using hsum

/-- All actual finite-support group-algebra elements preserve the flag. -/
theorem flagRepresentationAlgebra_mem_degree_zero
    (hF : Antitone F) (ρ : G →* (Module.End k E)ˣ)
    (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
      degreeRaisingEndomorphisms k E F 1) (a : MonoidAlgebra k G) :
    flagRepresentationAlgebra k G E ρ a ∈ degreeRaisingEndomorphisms k E F 0 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | single g c =>
    change MonoidAlgebra.lift k (Module.End k E) G
      ((Units.coeHom (Module.End k E)).comp ρ)
        (MonoidAlgebra.single g c) ∈ _
    rw [MonoidAlgebra.lift_single]
    exact Submodule.smul_mem _ c (flagRepresentation_mem_degree_zero k G E F hF ρ hρ g)

/-- The whole actual augmentation ideal is sent into the actual
degree-one operator space, by the proved original difference span. -/
theorem flagRepresentationAlgebra_augmentation_mem
    (ρ : G →* (Module.End k E)ˣ)
    (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
      degreeRaisingEndomorphisms k E F 1)
    (a : MonoidAlgebra k G) (ha : a ∈ GroupAlgebra.augmentationIdeal k G) :
    flagRepresentationAlgebra k G E ρ a ∈ degreeRaisingEndomorphisms k E F 1 := by
  have hspan : a ∈ Submodule.span k
      (Set.range (GroupAlgebra.augmentationDifference k G)) := by
    rw [← GroupAlgebra.augmentationLinearIdeal_eq_span]
    exact ha
  clear ha
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [flagRepresentationAlgebra_difference]
    exact hρ g
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _hx _hy hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _hx hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/-- Multiplication in the genuine noncommutative group algebra raises
the actual flag by the actual augmentation power. -/
theorem flagRepresentationAlgebra_augmentation_pow_mem
    (hF : Antitone F) (ρ : G →* (Module.End k E)ˣ)
    (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
      degreeRaisingEndomorphisms k E F 1) (q : ℕ)
    (a : MonoidAlgebra k G) (ha : a ∈ (GroupAlgebra.augmentationIdeal k G) ^ q) :
    flagRepresentationAlgebra k G E ρ a ∈ degreeRaisingEndomorphisms k E F q := by
  induction q generalizing a with
  | zero => exact flagRepresentationAlgebra_mem_degree_zero k G E F hF ρ hρ a
  | succ q ih =>
    rw [Submodule.pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [map_mul]
      exact mul_mem_degreeRaisingEndomorphisms k E F q 1 _ _ (ih x hx)
        (flagRepresentationAlgebra_augmentation_mem k G E F ρ hρ y hy)
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- Native term n is ordinary Gamma_(n+1), so its actual deviation
raises the actual flag by n+1. This uses the proved original augmentation
inclusion, not a guessed dimension-subgroup equality. -/
theorem lowerCentral_flagDeviation_mem
    (hF : Antitone F) (ρ : G →* (Module.End k E)ˣ)
    (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
      degreeRaisingEndomorphisms k E F 1) (n : ℕ) (g : G)
    (hg : g ∈ lowerCentralSeries G n) :
    (ρ g : Module.End k E) - 1 ∈ degreeRaisingEndomorphisms k E F (n + 1) := by
  have h := flagRepresentationAlgebra_augmentation_pow_mem k G E F hF ρ hρ
    (n + 1) (GroupAlgebra.augmentationDifference k G g)
    (GroupAlgebra.augmentationDifference_mem_pow_of_lowerCentralSeries k G n g hg)
  simpa only [flagRepresentationAlgebra_difference] using h

/-- These are the actual next operator filtration submodules inside the
actual current operator space. -/
def nextDegreeRaisingWithin (q : ℕ) :
    Submodule k (degreeRaisingEndomorphisms k E F q) :=
  (degreeRaisingEndomorphisms k E F (q + 1)).comap
    (degreeRaisingEndomorphisms k E F q).subtype

/-- The real native successive operator quotient. -/
abbrev DegreeRaisingPiece (q : ℕ) :=
  degreeRaisingEndomorphisms k E F q ⧸ nextDegreeRaisingWithin k E F q

/-- The actual multiplication error follows by applying the actual
group-ring homomorphism to the original noncommutative identity. -/
theorem flagRepresentation_deviation_mul
    (ρ : G →* (Module.End k E)ˣ) (g h : G) :
    (ρ (g * h) : Module.End k E) - 1 =
      ((ρ g : Module.End k E) - 1) + ((ρ h : Module.End k E) - 1) +
        ((ρ g : Module.End k E) - 1) * ((ρ h : Module.End k E) - 1) := by
  have hmul := congrArg (flagRepresentationAlgebra k G E ρ)
    (GroupAlgebra.augmentationDifference_mul k G g h)
  simpa only [map_add, map_mul, flagRepresentationAlgebra_difference] using hmul

variable (hF : Antitone F) (ρ : G →* (Module.End k E)ˣ)
variable (hρ : ∀ g : G, (ρ g : Module.End k E) - 1 ∈
  degreeRaisingEndomorphisms k E F 1)

/-- The actual current LCS element has its actual operator deviation
in the actual current raising space. -/
def lowerCentralFlagDifference (n : ℕ) (g : lowerCentralSeries G n) :
    degreeRaisingEndomorphisms k E F (n + 1) :=
  ⟨(ρ (g : G) : Module.End k E) - 1,
    lowerCentral_flagDeviation_mem k G E F hF ρ hρ n g g.property⟩

/-- The genuine current deviation is additive modulo the genuine next
operator space. The actual quadratic error is proved to lie there. -/
def lowerCentralFlagLeadingHom (n : ℕ) :
    lowerCentralSeries G n →* Multiplicative (DegreeRaisingPiece k E F (n + 1)) where
  toFun g := Multiplicative.ofAdd
    ((nextDegreeRaisingWithin k E F (n + 1)).mkQ
      (lowerCentralFlagDifference k G E F hF ρ hρ n g))
  map_one' := by
    change (nextDegreeRaisingWithin k E F (n + 1)).mkQ
      (lowerCentralFlagDifference k G E F hF ρ hρ n 1) = 0
    have hz : lowerCentralFlagDifference k G E F hF ρ hρ n 1 = 0 := by
      apply Subtype.ext
      change (ρ (1 : G) : Module.End k E) - 1 = 0
      rw [ρ.map_one, Units.val_one, sub_self]
    rw [hz, map_zero]
  map_mul' g h := by
    let a := lowerCentralFlagDifference k G E F hF ρ hρ n g
    let b := lowerCentralFlagDifference k G E F hF ρ hρ n h
    have hprod : (a : Module.End k E) * (b : Module.End k E) ∈
        degreeRaisingEndomorphisms k E F ((n + 1) + (n + 1)) :=
      mul_mem_degreeRaisingEndomorphisms k E F (n + 1) (n + 1)
        a b a.property b.property
    let err : degreeRaisingEndomorphisms k E F (n + 1) :=
      ⟨(a : Module.End k E) * (b : Module.End k E),
        degreeRaisingEndomorphisms_antitone k E F hF (n + 1)
          ((n + 1) + (n + 1)) (by omega) hprod⟩
    have herr : err ∈ nextDegreeRaisingWithin k E F (n + 1) :=
      degreeRaisingEndomorphisms_antitone k E F hF ((n + 1) + 1)
        ((n + 1) + (n + 1)) (by omega) hprod
    have heq : lowerCentralFlagDifference k G E F hF ρ hρ n (g * h) =
        a + b + err := by
      apply Subtype.ext
      exact flagRepresentation_deviation_mul k G E ρ (g : G) (h : G)
    have hz : (nextDegreeRaisingWithin k E F (n + 1)).mkQ err = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr herr
    change (nextDegreeRaisingWithin k E F (n + 1)).mkQ
        (lowerCentralFlagDifference k G E F hF ρ hρ n (g * h)) =
      (nextDegreeRaisingWithin k E F (n + 1)).mkQ a +
        (nextDegreeRaisingWithin k E F (n + 1)).mkQ b
    rw [heq, map_add, map_add, hz, add_zero]

/-- The original next native LCS subgroup is in the actual kernel,
because its actual deviation raises one more degree. -/
theorem nextLowerCentralIn_le_flagLeadingHom_ker (n : ℕ) :
    ChenRanks.nextLowerCentralIn G n ≤
      (lowerCentralFlagLeadingHom k G E F hF ρ hρ n).ker := by
  intro g hg
  change (nextDegreeRaisingWithin k E F (n + 1)).mkQ
    (lowerCentralFlagDifference k G E F hF ρ hρ n g) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (ρ (g : G) : Module.End k E) - 1 ∈
    degreeRaisingEndomorphisms k E F ((n + 1) + 1)
  exact lowerCentral_flagDeviation_mem k G E F hF ρ hρ (n + 1) g hg

/-- Actual descent through the same original successive group quotient. -/
def lowerCentralPieceFlagLeadingHom (n : ℕ) :
    ChenRanks.lowerCentralPiece G n →*
      Multiplicative (DegreeRaisingPiece k E F (n + 1)) :=
  QuotientGroup.lift (ChenRanks.nextLowerCentralIn G n)
    (lowerCentralFlagLeadingHom k G E F hF ρ hρ n)
    (nextLowerCentralIn_le_flagLeadingHom_ker k G E F hF ρ hρ n)

/-- The genuine additive character of the genuine original graded group
quotient, with values in the genuine operator filtration quotient. -/
def lowerCentralPieceFlagLeadingCharacter (n : ℕ) :
    Additive (ChenRanks.lowerCentralPiece G n) →+
      DegreeRaisingPiece k E F (n + 1) where
  toFun a := Multiplicative.toAdd
    (lowerCentralPieceFlagLeadingHom k G E F hF ρ hρ n (Additive.toMul a))
  map_zero' := (lowerCentralPieceFlagLeadingHom k G E F hF ρ hρ n).map_one
  map_add' a b := (lowerCentralPieceFlagLeadingHom k G E F hF ρ hρ n).map_mul
    (Additive.toMul a) (Additive.toMul b)

@[simp] theorem lowerCentralPieceFlagLeadingCharacter_mk (n : ℕ)
    (g : lowerCentralSeries G n) :
    lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ n
      (Additive.ofMul (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G n) g)) =
    (nextDegreeRaisingWithin k E F (n + 1)).mkQ
      (lowerCentralFlagDifference k G E F hF ρ hρ n g) := rfl

/-- Actual scalar extension of this same original graded group map. -/
def scalarLowerCentralFlagLeadingMap (n : ℕ) :
    ChenRanks.scalarLowerCentralPiece k G n →ₗ[k]
      DegreeRaisingPiece k E F (n + 1) :=
  AlgebraTensorModule.lift (R := ℤ) (A := k) (M := k)
    (N := Additive (ChenRanks.lowerCentralPiece G n))
    (P := DegreeRaisingPiece k E F (n + 1))
    (LinearMap.toSpanSingleton k
      (Additive (ChenRanks.lowerCentralPiece G n) →ₗ[ℤ]
        DegreeRaisingPiece k E F (n + 1))
      (lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ n).toIntLinearMap)

@[simp] theorem scalarLowerCentralFlagLeadingMap_tmul (n : ℕ) (c : k)
    (a : Additive (ChenRanks.lowerCentralPiece G n)) :
    scalarLowerCentralFlagLeadingMap k G E F hF ρ hρ n (c ⊗ₜ[ℤ] a) =
      c • lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ n a := by
  simp only [scalarLowerCentralFlagLeadingMap, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    AddMonoidHom.coe_toIntLinearMap]

/-- Actual ring commutators of actual raising operators add the
actual two raising degrees. -/
theorem commutator_mem_degreeRaisingEndomorphisms (q r : ℕ)
    (a b : Module.End k E)
    (ha : a ∈ degreeRaisingEndomorphisms k E F q)
    (hb : b ∈ degreeRaisingEndomorphisms k E F r) :
    a * b - b * a ∈ degreeRaisingEndomorphisms k E F (q + r) := by
  have hab := mul_mem_degreeRaisingEndomorphisms k E F q r a b ha hb
  have hba := mul_mem_degreeRaisingEndomorphisms k E F r q b a hb ha
  rw [Nat.add_comm r q] at hba
  exact Submodule.sub_mem _ hab hba

include hF hρ in
/-- The actual group commutator's leading operator is the genuine ring
commutator. The inverse factor contributes only the next raising degree. -/
theorem flagRepresentation_commutator_leading_error_mem (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    ((ρ ⁅(g : G), (h : G)⁆ : Module.End k E) - 1) -
        (((ρ (g : G) : Module.End k E) - 1) * ((ρ (h : G) : Module.End k E) - 1) -
          ((ρ (h : G) : Module.End k E) - 1) * ((ρ (g : G) : Module.End k E) - 1)) ∈
      degreeRaisingEndomorphisms k E F (((m + 1) + (n + 1)) + 1) := by
  let a : Module.End k E := (ρ (g : G) : Module.End k E) - 1
  let b : Module.End k E := (ρ (h : G) : Module.End k E) - 1
  let C : Module.End k E := a * b - b * a
  have hC : C ∈ degreeRaisingEndomorphisms k E F ((m + 1) + (n + 1)) :=
    commutator_mem_degreeRaisingEndomorphisms k E F (m + 1) (n + 1) a b
      (lowerCentral_flagDeviation_mem k G E F hF ρ hρ m g g.property)
      (lowerCentral_flagDeviation_mem k G E F hF ρ hρ n h h.property)
  have hc := congrArg (flagRepresentationAlgebra k G E ρ)
    (GroupAlgebra.augmentationDifference_commutator k G (g : G) (h : G))
  simp only [map_mul, map_sub, flagRepresentationAlgebra_difference,
    flagRepresentationAlgebra_of] at hc
  have hformula : (ρ ⁅(g : G), (h : G)⁆ : Module.End k E) - 1 =
      C * (ρ ((g : G)⁻¹ * (h : G)⁻¹) : Module.End k E) := by
    simpa only [C, a, b, ρ.map_mul, Units.val_mul] using hc
  have herr : C * (ρ ((g : G)⁻¹ * (h : G)⁻¹) : Module.End k E) - C =
      C * ((ρ ((g : G)⁻¹ * (h : G)⁻¹) : Module.End k E) - 1) := by
    noncomm_ring
  change ((ρ ⁅(g : G), (h : G)⁆ : Module.End k E) - 1) - C ∈ _
  rw [hformula, herr]
  exact mul_mem_degreeRaisingEndomorphisms k E F ((m + 1) + (n + 1)) 1 _ _
    hC (hρ ((g : G)⁻¹ * (h : G)⁻¹))

/-- The true ring-commutator representative is in the same actual
operator degree as the original native group commutator. -/
def lowerCentralFlagCommutatorRepresentative (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    degreeRaisingEndomorphisms k E F ((m + n + 1) + 1) :=
  ⟨((ρ (g : G) : Module.End k E) - 1) * ((ρ (h : G) : Module.End k E) - 1) -
      ((ρ (h : G) : Module.End k E) - 1) * ((ρ (g : G) : Module.End k E) - 1), by
    have hmem := commutator_mem_degreeRaisingEndomorphisms k E F
      (m + 1) (n + 1) _ _
      (lowerCentral_flagDeviation_mem k G E F hF ρ hρ m g g.property)
      (lowerCentral_flagDeviation_mem k G E F hF ρ hρ n h h.property)
    simpa only [show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega] using hmem⟩

/-- The actual leading character respects the actual original quotient
commutator on original representatives. This is a genuine equality in
J_(m+n+2)/J_(m+n+3), not an assumed bracket-detection formula. -/
theorem lowerCentralPieceFlagLeadingCharacter_bracket_mk_mk (m n : ℕ)
    (g : lowerCentralSeries G m) (h : lowerCentralSeries G n) :
    lowerCentralPieceFlagLeadingCharacter k G E F hF ρ hρ (m + n + 1)
      (Additive.ofMul (ChenRanks.lowerCentralPieceBracket G m n
        (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G m) g)
        (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G n) h))) =
      (nextDegreeRaisingWithin k E F ((m + n + 1) + 1)).mkQ
        (lowerCentralFlagCommutatorRepresentative k G E F hF ρ hρ m n g h) := by
  rw [ChenRanks.lowerCentralPieceBracket_mk_mk,
    lowerCentralPieceFlagLeadingCharacter_mk]
  apply (Submodule.Quotient.eq _).mpr
  change ((ρ ⁅(g : G), (h : G)⁆ : Module.End k E) - 1) -
      (((ρ (g : G) : Module.End k E) - 1) * ((ρ (h : G) : Module.End k E) - 1) -
        ((ρ (h : G) : Module.End k E) - 1) * ((ρ (g : G) : Module.End k E) - 1)) ∈
    degreeRaisingEndomorphisms k E F (((m + n + 1) + 1) + 1)
  simpa only [show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega] using
    flagRepresentation_commutator_leading_error_mem k G E F hF ρ hρ m n g h

end ChenRanks.LieComparison
