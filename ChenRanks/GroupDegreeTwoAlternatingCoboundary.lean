import ChenRanks.GroupCommutatorDegreeTwoCharacter
import ChenRanks.AdditiveCocycleAlternatingPart
import ChenRanks.GroupCharacterCup
import ChenRanks.GroupLowerCentralDegreeOne
import Mathlib.Tactic.Group

/-! Actual degree-two commutator characters give genuine coboundaries in
the original native group bar complex. The actual section remainder and
its multiplication law are constructed in the original group. Symmetric
splitting is derived by Baer extension over the characteristic-zero field.
Neither cup-kernel containment nor a cochain primitive is an input.
-/

noncomputable section
open scoped commutatorElement
namespace ChenRanks.GroupComparison

variable (G k : Type) [Group G] [Field k] [CharZero k]

/-- The original group element's actual abelianization coordinate. -/
def originalAbelianizationCoordinate (g : G) : Additive (Abelianization G) :=
  Additive.ofMul (Abelianization.of g)

@[simp] theorem originalAbelianizationCoordinate_mul (g h : G) :
    originalAbelianizationCoordinate G (g * h) =
      originalAbelianizationCoordinate G g + originalAbelianizationCoordinate G h := by
  change Additive.ofMul (Abelianization.of (g * h)) = _
  rw [map_mul, ofMul_mul]
  rfl

/-- The genuine remainder lies in the original commutator subgroup. -/
def originalAbelianizationRemainder (g : G) : commutator G :=
  ⟨g * (normalizedAbelianizationSection G (Abelianization.of g))⁻¹, by
    have hm : g * (normalizedAbelianizationSection G (Abelianization.of g))⁻¹ ∈
        (Abelianization.of : G →* Abelianization G).ker := by
      change Abelianization.of
        (g * (normalizedAbelianizationSection G (Abelianization.of g))⁻¹) = 1
      rw [map_mul, map_inv, normalizedAbelianizationSection_projection, mul_inv_cancel]
    simpa only [Abelianization.ker_of] using hm⟩

/-- The actual multiplication error of the actual remainders. -/
theorem originalAbelianizationRemainder_mul (g h : G) :
    originalAbelianizationRemainder G (g * h) =
      originalAbelianizationRemainder G g *
        originalCommutatorConjugate G
          (normalizedAbelianizationSection G (Abelianization.of g))
          (originalAbelianizationRemainder G h) *
        abelianizationSectionError G
          (originalAbelianizationCoordinate G g) (originalAbelianizationCoordinate G h) := by
  apply Subtype.ext
  change g * h * (normalizedAbelianizationSection G (Abelianization.of (g * h)))⁻¹ =
    (g * (normalizedAbelianizationSection G (Abelianization.of g))⁻¹) *
    (normalizedAbelianizationSection G (Abelianization.of g) *
      (h * (normalizedAbelianizationSection G (Abelianization.of h))⁻¹) *
      (normalizedAbelianizationSection G (Abelianization.of g))⁻¹) *
    (normalizedAbelianizationSection G (Abelianization.of g) *
      normalizedAbelianizationSection G (Abelianization.of h) *
      (normalizedAbelianizationSection G
        (Abelianization.of g * Abelianization.of h))⁻¹)
  rw [map_mul]
  group

/-- Genuine normalized cocycle data of the actual quotient character. -/
def degreeTwoCharacterSectionCocycleData
    (χ : Additive (lowerCentralPiece G 1) →+ k) :
    NormalizedAdditiveCocycle (Additive (Abelianization G)) k where
  toFun := commutatorDegreeTwoSectionCocycle G k χ
  zero_right := commutatorDegreeTwoSectionCocycle_zero_right G k χ
  zero_left a := by
    unfold commutatorDegreeTwoSectionCocycle
    rw [abelianizationSectionError_zero_left]
    exact (commutatorDegreeTwoCharacter G k χ).map_zero
  cocycle := commutatorDegreeTwoSectionCocycle_identity G k χ

/-- The actual original commutator as an element of the original kernel. -/
def originalCommutatorElement (g h : G) : commutator G :=
  ⟨⁅g, h⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
    (Subgroup.mem_top h)⟩

/-- The actual first successive-quotient class of an original element. -/
def originalFirstLowerCentralClass (g : G) : lowerCentralPiece G 0 :=
  QuotientGroup.mk' (nextLowerCentralIn G 0) ⟨g, Subgroup.mem_top g⟩

theorem originalFirstLowerCentralClass_section (g : G) :
    originalFirstLowerCentralClass G
      (normalizedAbelianizationSection G (Abelianization.of g)) =
      originalFirstLowerCentralClass G g := by
  apply (lowerCentralDegreeOneAbelianizationEquiv G).injective
  change Abelianization.of
      (normalizedAbelianizationSection G (Abelianization.of g)) = Abelianization.of g
  exact normalizedAbelianizationSection_projection G _

theorem originalCommutatorElement_degreeTwoProjection (g h : G) :
    commutatorDegreeTwoProjection G (originalCommutatorElement G g h) =
      lowerCentralPieceBracket G 0 0
        (originalFirstLowerCentralClass G g) (originalFirstLowerCentralClass G h) := by
  rw [originalFirstLowerCentralClass, originalFirstLowerCentralClass,
    lowerCentralPieceBracket_mk_mk]
  rfl

/-- The actual antisymmetric section cocycle pulled back to the original G. -/
def degreeTwoCharacterAlternatingCochain
    (χ : Additive (lowerCentralPiece G 1) →+ k) (g h : G) : k :=
  cocycleAlternatingPart (degreeTwoCharacterSectionCocycleData G k χ)
    (originalAbelianizationCoordinate G g) (originalAbelianizationCoordinate G h)

/-- The actual alternating cochain is precisely the character of the
actual original degree-two bracket, with the native sign convention. -/
theorem degreeTwoCharacterAlternatingCochain_eq_actual_bracket
    (χ : Additive (lowerCentralPiece G 1) →+ k) (g h : G) :
    degreeTwoCharacterAlternatingCochain G k χ g h =
      χ (Additive.ofMul (lowerCentralPieceBracket G 0 0
        (originalFirstLowerCentralClass G g) (originalFirstLowerCentralClass G h))) := by
  let a := originalAbelianizationCoordinate G g
  let b := originalAbelianizationCoordinate G h
  have heq : abelianizationSectionError G a b *
      (abelianizationSectionError G b a)⁻¹ =
      originalCommutatorElement G (normalizedAbelianizationSection G a.toMul)
        (normalizedAbelianizationSection G b.toMul) :=
    Subtype.ext (abelianizationSectionError_skew G a b)
  have hc := congrArg (fun n : commutator G =>
    commutatorDegreeTwoCharacter G k χ (Additive.ofMul n)) heq
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg] at hc
  change commutatorDegreeTwoCharacter G k χ (Additive.ofMul (abelianizationSectionError G a b)) -
      commutatorDegreeTwoCharacter G k χ (Additive.ofMul (abelianizationSectionError G b a)) = _
  calc
    _ = commutatorDegreeTwoCharacter G k χ
        (Additive.ofMul (originalCommutatorElement G
          (normalizedAbelianizationSection G a.toMul)
          (normalizedAbelianizationSection G b.toMul))) := by
      simpa only [sub_eq_add_neg] using hc
    _ = χ (Additive.ofMul (lowerCentralPieceBracket G 0 0
        (originalFirstLowerCentralClass G
          (normalizedAbelianizationSection G (Abelianization.of g)))
        (originalFirstLowerCentralClass G
          (normalizedAbelianizationSection G (Abelianization.of h))))) := by
      change χ (Additive.ofMul (commutatorDegreeTwoProjection G
        (originalCommutatorElement G
          (normalizedAbelianizationSection G (Abelianization.of g))
          (normalizedAbelianizationSection G (Abelianization.of h))))) = _
      rw [originalCommutatorElement_degreeTwoProjection]
    _ = _ := by rw [originalFirstLowerCentralClass_section,
      originalFirstLowerCentralClass_section]

/-- A genuine bar primitive, constructed from the original group rather
than assumed. -/
theorem degreeTwoCharacterAlternating_has_primitive
    (χ : Additive (lowerCentralPiece G 1) →+ k) :
    ∃ F : G → k, ∀ g h,
      F h - F (g * h) + F g = degreeTwoCharacterAlternatingCochain G k χ g h := by
  let c := degreeTwoCharacterSectionCocycleData G k χ
  obtain ⟨f, hf⟩ := additiveCocycle_has_symmetric_primitive c
  let μ := commutatorDegreeTwoCharacter G k χ
  refine ⟨fun g => -(2 : k) *
    (μ (Additive.ofMul (originalAbelianizationRemainder G g)) +
      f (originalAbelianizationCoordinate G g)), ?_⟩
  intro g h
  have hm := congrArg (fun n : commutator G => μ (Additive.ofMul n))
    (originalAbelianizationRemainder_mul G g h)
  simp only [μ, ofMul_mul, map_add, commutatorDegreeTwoCharacter_conjugate] at hm
  change μ (Additive.ofMul (originalAbelianizationRemainder G (g * h))) =
      μ (Additive.ofMul (originalAbelianizationRemainder G g)) +
      μ (Additive.ofMul (originalAbelianizationRemainder G h)) +
      commutatorDegreeTwoSectionCocycle G k χ
        (originalAbelianizationCoordinate G g) (originalAbelianizationCoordinate G h) at hm
  have hfgh := hf (originalAbelianizationCoordinate G g)
    (originalAbelianizationCoordinate G h)
  change commutatorDegreeTwoSectionCocycle G k χ
      (originalAbelianizationCoordinate G g) (originalAbelianizationCoordinate G h) -
      (f (originalAbelianizationCoordinate G h) -
        f (originalAbelianizationCoordinate G g + originalAbelianizationCoordinate G h) +
        f (originalAbelianizationCoordinate G g)) = _ at hfgh
  change -(2 : k) * (μ (Additive.ofMul (originalAbelianizationRemainder G h)) +
      f (originalAbelianizationCoordinate G h)) -
    (-(2 : k) * (μ (Additive.ofMul (originalAbelianizationRemainder G (g * h))) +
      f (originalAbelianizationCoordinate G (g * h)))) +
    -(2 : k) * (μ (Additive.ofMul (originalAbelianizationRemainder G g)) +
      f (originalAbelianizationCoordinate G g)) = _
  rw [originalAbelianizationCoordinate_mul, hm]
  change _ = cocycleAlternatingPart c
    (originalAbelianizationCoordinate G g) (originalAbelianizationCoordinate G h)
  field_simp at hfgh
  linear_combination hfgh

/-- This is the actual cocycle in the native original bar complex. -/
def degreeTwoCharacterAlternatingCocycle
    (χ : Additive (lowerCentralPiece G 1) →+ k) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k G) := by
  refine ⟨fun gh => degreeTwoCharacterAlternatingCochain G k χ gh.1 gh.2, ?_⟩
  apply (groupCohomology.mem_cocycles₂_def _).mpr
  intro g h j
  simp only [Representation.trivial_apply, degreeTwoCharacterAlternatingCochain,
    originalAbelianizationCoordinate_mul, cocycleAlternatingPart_add_left,
    cocycleAlternatingPart_add_right]
  abel

/-- The actual native H² class vanishes by the actual bar primitive. -/
theorem degreeTwoCharacterAlternating_nativeH2_zero
    (χ : Additive (lowerCentralPiece G 1) →+ k) :
    groupCohomology.H2π (groupTrivialCoefficients k G)
      (degreeTwoCharacterAlternatingCocycle G k χ) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  obtain ⟨F, hF⟩ := degreeTwoCharacterAlternating_has_primitive G k χ
  refine ⟨F, ?_⟩
  funext gh
  simp only [groupCohomology.d₁₂_hom_apply]
  exact hF gh.1 gh.2

end ChenRanks.GroupComparison
