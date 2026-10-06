import ChenRanks.ChenObjects

/-!
# Actual central-series quotients under an abelian direct factor

The central-arrangement reduction in the manuscript uses an actual group
product with an infinite cyclic group. This module proves the group-theoretic
part for any abelian factor: its genuine derived and lower central series
are computed inside the original product group. The maximal metabelian
quotient is compared by the actual quotient homomorphism.

No topological deconing equivalence or Chen comparison is supplied here.
-/

noncomputable section

namespace ChenRanks

open scoped commutatorElement

variable (G H : Type*) [Group G] [Group H]

/-- Derived series of the actual direct product, proved by commutator
functoriality on the genuine product subgroups. -/
theorem derivedSeries_product (n : ℕ) :
    derivedSeries (G × H) n = (derivedSeries G n).prod (derivedSeries H n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivedSeries_succ, ih, Subgroup.commutator_prod_prod,
      ← derivedSeries_succ, ← derivedSeries_succ]

variable (A : Type*) [CommGroup A]

/-- An abelian factor contributes no positive derived-series term. -/
theorem abelian_derivedSeries_succ (n : ℕ) : derivedSeries A (n + 1) = ⊥ := by
  apply bot_unique
  have h := derivedSeries_antitone (G := A) (show 1 ≤ n + 1 by omega)
  rw [derivedSeries_one, (commutator_eq_bot_iff_center_eq_top A).mpr CommGroup.center_eq_top] at h
  exact h

/-- An abelian factor contributes no lower-central term after degree one. -/
theorem abelian_lowerCentralSeries_succ (n : ℕ) :
    lowerCentralSeries A (n + 1) = ⊥ := by
  apply bot_unique
  have h := lowerCentralSeries_antitone (G := A) (show 1 ≤ n + 1 by omega)
  rw [lowerCentralSeries_one,
    (commutator_eq_bot_iff_center_eq_top A).mpr CommGroup.center_eq_top] at h
  exact h

/-- The actual quotient homomorphism on the product. -/
def metabelianProductMap : G × A →* metabelianQuotient G × A :=
  (QuotientGroup.mk' (derivedSeries G 2)).prodMap (MonoidHom.id A)

/-- Its genuine kernel is the product's second derived subgroup. -/
theorem metabelianProductMap_kernel :
    (metabelianProductMap G A).ker = derivedSeries (G × A) 2 := by
  rw [derivedSeries_product, show derivedSeries A 2 = ⊥ from abelian_derivedSeries_succ A 1]
  ext x
  change ((QuotientGroup.mk' (derivedSeries G 2)) x.1, x.2) = (1, 1) ↔
    x.1 ∈ derivedSeries G 2 ∧ x.2 ∈ (⊥ : Subgroup A)
  rw [Prod.mk.injEq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_bot]

/-- The map is surjective by the actual quotient's surjectivity. -/
theorem metabelianProductMap_surjective : Function.Surjective (metabelianProductMap G A) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (derivedSeries G 2) x.1
  exact ⟨(g, x.2), Prod.ext hg rfl⟩

/-- The maximal metabelian quotient of the original product is the
actual metabelian quotient times its original abelian factor. -/
def metabelianProductEquiv :
    metabelianQuotient (G × A) ≃* metabelianQuotient G × A :=
  (QuotientGroup.quotientMulEquivOfEq (metabelianProductMap_kernel G A).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (metabelianProductMap G A)
      (metabelianProductMap_surjective G A))

end ChenRanks
