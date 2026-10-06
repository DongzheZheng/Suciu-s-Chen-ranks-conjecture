import ChenRanks.GroupLowerCentralPieceBracket
import ChenRanks.GroupAbelianizationSectionCocycle

/-! A character of the original second lower-central successive quotient
gives an actual conjugation-invariant character of the original commutator
subgroup. Applying that character to the actual normalized abelianization
section gives an actual additive two-cocycle. All invariance and cocycle
identities are derived from the original group and its original quotients;
no cup/holonomy comparison or group formality is supplied.
-/

noncomputable section

namespace ChenRanks.GroupComparison

variable (G : Type*) [Group G]

/-- The actual second-degree projection on the original commutator. -/
def commutatorDegreeTwoProjection : commutator G →* lowerCentralPiece G 1 where
  toFun n := QuotientGroup.mk' (nextLowerCentralIn G 1)
    ⟨(n : G), by simpa only [lowerCentralSeries_one] using n.property⟩
  map_one' := by
    change QuotientGroup.mk' (nextLowerCentralIn G 1)
      (1 : lowerCentralSeries G 1) = 1
    exact (QuotientGroup.mk' (nextLowerCentralIn G 1)).map_one
  map_mul' n m := by
    change QuotientGroup.mk' (nextLowerCentralIn G 1)
      ((⟨(n : G), by simpa only [lowerCentralSeries_one] using n.property⟩ :
          lowerCentralSeries G 1) *
       (⟨(m : G), by simpa only [lowerCentralSeries_one] using m.property⟩ :
          lowerCentralSeries G 1)) = _
    exact (QuotientGroup.mk' (nextLowerCentralIn G 1)).map_mul _ _

@[simp] theorem commutatorDegreeTwoProjection_ambient (n : commutator G) :
    lowerCentralPieceAmbientHom G 1 (commutatorDegreeTwoProjection G n) =
      QuotientGroup.mk' (lowerCentralSeries G 2) (n : G) := rfl

/-- Conjugation remains in the original commutator kernel. -/
def originalCommutatorConjugate (g : G) (n : commutator G) : commutator G :=
  ⟨g * (n : G) * g⁻¹, by
    have hn : Abelianization.of (n : G) = 1 := by
      change (n : G) ∈ (Abelianization.of : G →* Abelianization G).ker
      simpa only [Abelianization.ker_of] using n.property
    have hm : g * (n : G) * g⁻¹ ∈
        (Abelianization.of : G →* Abelianization G).ker := by
      change Abelianization.of (g * (n : G) * g⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hn, mul_one, mul_inv_cancel]
    simpa only [Abelianization.ker_of] using hm⟩

/-- The actual quotient internally kills the actual conjugation error. -/
theorem commutatorDegreeTwoProjection_conjugate (g : G) (n : commutator G) :
    commutatorDegreeTwoProjection G (originalCommutatorConjugate G g n) =
      commutatorDegreeTwoProjection G n := by
  apply lowerCentralPieceAmbientHom_injective G 1
  rw [commutatorDegreeTwoProjection_ambient, commutatorDegreeTwoProjection_ambient]
  change QuotientGroup.mk' (lowerCentralSeries G 2) (g * (n : G) * g⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  have hc := lowerCentral_ambient_image_commute G 1 (n : G)
    (by simpa only [lowerCentralSeries_one] using n.property) g
  rw [hc.eq.symm, mul_assoc, mul_inv_cancel, mul_one]

variable (M : Type*) [AddCommGroup M]

/-- An actual quotient character, pulled back to the actual commutator. -/
def commutatorDegreeTwoCharacter (χ : Additive (lowerCentralPiece G 1) →+ M) :
    Additive (commutator G) →+ M where
  toFun n := χ (Additive.ofMul (commutatorDegreeTwoProjection G n.toMul))
  map_zero' := by
    change χ (Additive.ofMul (commutatorDegreeTwoProjection G 1)) = 0
    rw [map_one]
    exact χ.map_zero
  map_add' n m := by
    change χ (Additive.ofMul (commutatorDegreeTwoProjection G (n.toMul * m.toMul))) = _
    rw [map_mul, ofMul_mul]
    exact χ.map_add _ _

theorem commutatorDegreeTwoCharacter_conjugate
    (χ : Additive (lowerCentralPiece G 1) →+ M) (g : G) (n : commutator G) :
    commutatorDegreeTwoCharacter G M χ
      (Additive.ofMul (originalCommutatorConjugate G g n)) =
      commutatorDegreeTwoCharacter G M χ (Additive.ofMul n) := by
  change χ (Additive.ofMul (commutatorDegreeTwoProjection G
    (originalCommutatorConjugate G g n))) = _
  rw [commutatorDegreeTwoProjection_conjugate]
  rfl

/-- The actual two-cochain of the actual abelianization section. -/
def commutatorDegreeTwoSectionCocycle
    (χ : Additive (lowerCentralPiece G 1) →+ M)
    (a b : Additive (Abelianization G)) : M :=
  commutatorDegreeTwoCharacter G M χ (Additive.ofMul (abelianizationSectionError G a b))

@[simp] theorem commutatorDegreeTwoSectionCocycle_zero_right
    (χ : Additive (lowerCentralPiece G 1) →+ M) (a : Additive (Abelianization G)) :
    commutatorDegreeTwoSectionCocycle G M χ a 0 = 0 := by
  unfold commutatorDegreeTwoSectionCocycle
  rw [abelianizationSectionError_zero_right]
  exact (commutatorDegreeTwoCharacter G M χ).map_zero

/-- A genuine additive cocycle identity, derived before any cohomology
or holonomy comparison is made. -/
theorem commutatorDegreeTwoSectionCocycle_identity
    (χ : Additive (lowerCentralPiece G 1) →+ M)
    (a b d : Additive (Abelianization G)) :
    commutatorDegreeTwoSectionCocycle G M χ a b +
      commutatorDegreeTwoSectionCocycle G M χ (a + b) d =
      commutatorDegreeTwoSectionCocycle G M χ b d +
        commutatorDegreeTwoSectionCocycle G M χ a (b + d) := by
  have heq : abelianizationSectionError G a b * abelianizationSectionError G (a + b) d =
      originalCommutatorConjugate G (normalizedAbelianizationSection G a.toMul)
        (abelianizationSectionError G b d) * abelianizationSectionError G a (b + d) :=
    Subtype.ext (abelianizationSectionError_cocycle G a b d)
  have h := congrArg (fun n : commutator G =>
    commutatorDegreeTwoCharacter G M χ (Additive.ofMul n)) heq
  simpa only [ofMul_mul, map_add, commutatorDegreeTwoCharacter_conjugate,
    commutatorDegreeTwoSectionCocycle] using h

end ChenRanks.GroupComparison
