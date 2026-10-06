import ChenRanks.ChenObjects
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The actual first lower-central quotient and abelianization

The original quotient `Γ₁(G)/Γ₂(G)` is identified with the native
`Abelianization G` by its genuine quotient universal property.  Taking
the original maximal metabelian quotient leaves this abelianization
unchanged.  Scalar extension therefore identifies the actual first Chen
space with the rationalization of the original abelianization.

This is a degree-one theorem for every group.  No higher dimension
subgroup theorem, formality, Malcev comparison, or Chen formula is used.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

/-- The actual abelian projection on the actual first lower-central term. -/
def lowerCentralDegreeOneProjection :
    lowerCentralSeries G 0 →* Abelianization G :=
  (Abelianization.of : G →* Abelianization G).comp
    (lowerCentralSeries G 0).subtype

@[simp] theorem lowerCentralDegreeOneProjection_apply
    (g : lowerCentralSeries G 0) :
    lowerCentralDegreeOneProjection G g = Abelianization.of (g : G) := rfl

theorem lowerCentralDegreeOneProjection_surjective :
    Function.Surjective (lowerCentralDegreeOneProjection G) := by
  intro a
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (commutator G) a
  refine ⟨⟨g, Subgroup.mem_top g⟩, ?_⟩
  exact hg

/-- Its actual kernel is the native next lower-central term, not an
assumed presentation of abelianization. -/
theorem lowerCentralDegreeOneProjection_ker :
    (lowerCentralDegreeOneProjection G).ker = nextLowerCentralIn G 0 := by
  ext g
  change Abelianization.of (g : G) = 1 ↔
    (g : G) ∈ lowerCentralSeries G (0 + 1)
  rw [lowerCentralSeries_one]
  change (g : G) ∈ (Abelianization.of : G →* Abelianization G).ker ↔
    (g : G) ∈ commutator G
  rw [Abelianization.ker_of]

/-- The genuine first lower-central quotient is the original native
abelianization. -/
def lowerCentralDegreeOneAbelianizationEquiv :
    lowerCentralPiece G 0 ≃* Abelianization G :=
  QuotientGroup.liftEquiv (nextLowerCentralIn G 0)
    (lowerCentralDegreeOneProjection_surjective G)
    (lowerCentralDegreeOneProjection_ker G).symm

@[simp] theorem lowerCentralDegreeOneAbelianizationEquiv_mk
    (g : lowerCentralSeries G 0) :
    lowerCentralDegreeOneAbelianizationEquiv G
      (QuotientGroup.mk' (nextLowerCentralIn G 0) g) =
      Abelianization.of (g : G) := rfl

section QuotientBelowCommutator

variable (N : Subgroup G) [N.Normal] (hN : N ≤ commutator G)

/-- The original abelian projection really descends through any normal
subgroup contained in the original commutator subgroup. -/
def quotientBelowCommutatorProjection : G ⧸ N →* Abelianization G :=
  QuotientGroup.lift N Abelianization.of (by
    rw [Abelianization.ker_of]
    exact hN)

@[simp] theorem quotientBelowCommutatorProjection_mk (g : G) :
    quotientBelowCommutatorProjection G N hN (QuotientGroup.mk' N g) =
      Abelianization.of g := rfl

/-- The two native abelianization maps are mutual inverses, proved on
the original group representatives in both actual quotients. -/
def quotientBelowCommutatorAbelianizationEquiv :
    Abelianization G ≃* Abelianization (G ⧸ N) where
  toFun := Abelianization.map (QuotientGroup.mk' N)
  invFun := Abelianization.lift (quotientBelowCommutatorProjection G N hN)
  left_inv a := by
    induction a using QuotientGroup.induction_on with
    | H g =>
      change Abelianization.lift (quotientBelowCommutatorProjection G N hN)
        (Abelianization.map (QuotientGroup.mk' N) (Abelianization.of g)) =
          Abelianization.of g
      rw [Abelianization.map_of, Abelianization.lift_apply_of,
        quotientBelowCommutatorProjection_mk]
  right_inv a := by
    induction a using QuotientGroup.induction_on with
    | H q =>
      induction q using QuotientGroup.induction_on with
      | H g =>
        change Abelianization.map (QuotientGroup.mk' N)
          (Abelianization.lift (quotientBelowCommutatorProjection G N hN)
            (Abelianization.of (QuotientGroup.mk' N g))) =
              Abelianization.of (QuotientGroup.mk' N g)
        rw [Abelianization.lift_apply_of,
          quotientBelowCommutatorProjection_mk, Abelianization.map_of]
  map_mul' := (Abelianization.map (QuotientGroup.mk' N)).map_mul

@[simp] theorem quotientBelowCommutatorAbelianizationEquiv_of (g : G) :
    quotientBelowCommutatorAbelianizationEquiv G N hN (Abelianization.of g) =
      Abelianization.of (QuotientGroup.mk' N g) := rfl

@[simp] theorem quotientBelowCommutatorAbelianizationEquiv_symm_of_mk (g : G) :
    (quotientBelowCommutatorAbelianizationEquiv G N hN).symm
      (Abelianization.of (QuotientGroup.mk' N g)) = Abelianization.of g := rfl

end QuotientBelowCommutator

/-- The actual second derived subgroup lies in the first one. -/
theorem secondDerived_le_commutator : derivedSeries G 2 ≤ commutator G := by
  simpa only [derivedSeries_one] using
    derivedSeries_antitone G (show (1 : ℕ) ≤ 2 by decide)

/-- Taking the genuine maximal metabelian quotient preserves the
original native abelianization. -/
def metabelianAbelianizationEquiv :
    Abelianization G ≃* Abelianization (metabelianQuotient G) :=
  quotientBelowCommutatorAbelianizationEquiv G (derivedSeries G 2)
    (secondDerived_le_commutator G)

@[simp] theorem metabelianAbelianizationEquiv_of (g : G) :
    metabelianAbelianizationEquiv G (Abelianization.of g) =
      Abelianization.of (QuotientGroup.mk' (derivedSeries G 2) g) := rfl

@[simp] theorem metabelianAbelianizationEquiv_symm_of_mk (g : G) :
    (metabelianAbelianizationEquiv G).symm
      (Abelianization.of (QuotientGroup.mk' (derivedSeries G 2) g)) =
      Abelianization.of g := rfl

/-- The actual first Chen quotient, before tensoring, is the
abelianization of the original group. -/
def chenDegreeOneAbelianizationEquiv :
    lowerCentralPiece (metabelianQuotient G) 0 ≃* Abelianization G :=
  (lowerCentralDegreeOneAbelianizationEquiv (metabelianQuotient G)).trans
    (metabelianAbelianizationEquiv G).symm

@[simp] theorem chenDegreeOneAbelianizationEquiv_mk (g : G) :
    chenDegreeOneAbelianizationEquiv G
      (QuotientGroup.mk' (nextLowerCentralIn (metabelianQuotient G) 0)
        ⟨QuotientGroup.mk' (derivedSeries G 2) g,
          Subgroup.mem_top _⟩) = Abelianization.of g := rfl

/-- An actual integral linear equivalence between the additive forms
of the original first Chen quotient and original abelianization. -/
def chenDegreeOneIntegralAbelianizationEquiv :
    Additive (lowerCentralPiece (metabelianQuotient G) 0) ≃ₗ[ℤ]
      Additive (Abelianization G) :=
  (chenDegreeOneAbelianizationEquiv G).toAdditive.toIntLinearEquiv

/-- True scalar extension of the original integral equivalence. -/
def rationalChenDegreeOneAbelianizationEquiv :
    rationalChenSpace G 0 ≃ₗ[ℚ] ℚ ⊗[ℤ] Additive (Abelianization G) :=
  AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (chenDegreeOneIntegralAbelianizationEquiv G)

@[simp] theorem rationalChenDegreeOneAbelianizationEquiv_tmul
    (c : ℚ) (g : G) :
    rationalChenDegreeOneAbelianizationEquiv G
      (c ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn (metabelianQuotient G) 0)
          ⟨QuotientGroup.mk' (derivedSeries G 2) g, Subgroup.mem_top _⟩)) =
        c ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g) := rfl

end ChenRanks
