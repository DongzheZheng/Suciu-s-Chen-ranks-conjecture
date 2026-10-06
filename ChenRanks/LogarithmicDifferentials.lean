import Mathlib

/-!
# Actual logarithmic Kähler differentials

The finite-product identity in the valuation-kernel argument is proved in
mathlib's actual module of Kähler differentials. It is not a formal symbol
with a stipulated product rule. This module does not assert the geometric
claim that a function without horizontal zeros or poles is constant on
general fibres.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

/-- The logarithmic differential of an actual nonzero function. -/
def logarithmicDifferential (u : Fˣ) : Ω[F⁄k] :=
  (u : F)⁻¹ • KaehlerDifferential.D k F (u : F)

@[simp]
theorem logarithmicDifferential_one :
    logarithmicDifferential k F 1 = 0 := by
  simp [logarithmicDifferential]

theorem logarithmicDifferential_mul (u v : Fˣ) :
    logarithmicDifferential k F (u * v) =
      logarithmicDifferential k F u + logarithmicDifferential k F v := by
  have hu : (u : F) ≠ 0 := Units.ne_zero u
  have hv : (v : F) ≠ 0 := Units.ne_zero v
  have h₁ : ((u : F) * (v : F))⁻¹ * (u : F) = (v : F)⁻¹ := by
    field_simp
  have h₂ : ((u : F) * (v : F))⁻¹ * (v : F) = (u : F)⁻¹ := by
    field_simp
  simp only [logarithmicDifferential, Units.val_mul, Derivation.leibniz,
    smul_add, smul_smul, h₁, h₂]
  exact add_comm _ _

/-- Multiplication of nonzero functions becomes addition of logarithmic
differentials; all identities follow from the universal derivation. -/
def logarithmicDifferentialHom : Fˣ →* Multiplicative Ω[F⁄k] where
  toFun u := Multiplicative.ofAdd (logarithmicDifferential k F u)
  map_one' := by simp
  map_mul' u v := by
    change Multiplicative.ofAdd (logarithmicDifferential k F (u * v)) =
      Multiplicative.ofAdd (logarithmicDifferential k F u +
        logarithmicDifferential k F v)
    rw [logarithmicDifferential_mul]

theorem logarithmicDifferential_zpow (u : Fˣ) (n : ℤ) :
    logarithmicDifferential k F (u ^ n) = n • logarithmicDifferential k F u := by
  have h := congrArg Multiplicative.toAdd
    (map_zpow (logarithmicDifferentialHom k F) u n)
  simpa only [logarithmicDifferentialHom, MonoidHom.coe_mk,
    toAdd_ofAdd, toAdd_zpow] using h

theorem logarithmicDifferential_prod {ι : Type*} (s : Finset ι) (u : ι → Fˣ) :
    logarithmicDifferential k F (∏ i ∈ s, u i) =
      ∑ i ∈ s, logarithmicDifferential k F (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, logarithmicDifferential_mul,
      Finset.sum_insert hi, ih]

/-- The exact identity used for the integral valuation-kernel vectors. -/
theorem logarithmicDifferential_prod_zpow {ι : Type*}
    (s : Finset ι) (u : ι → Fˣ) (n : ι → ℤ) :
    logarithmicDifferential k F (∏ i ∈ s, u i ^ n i) =
      ∑ i ∈ s, n i • logarithmicDifferential k F (u i) := by
  rw [logarithmicDifferential_prod]
  simp only [logarithmicDifferential_zpow]

end ChenRanks
