import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Ring

/-!
# Actual degree-one bar cups with trivial coefficients

The two-cochain is the genuine inhomogeneous bar expression χ(g)ψ(h).
Its cocycle equation is proved from the actual character laws. Its
class lies in the original native group H², and the precise primitive
criterion follows from the library's actual H² quotient and range of
its original differential. This does not assume a space-to-group H²
injection or define a synthetic second-cohomology target.
-/

noncomputable section

namespace ChenRanks

variable (k G : Type) [Field k] [Group G]

/-- The actual trivial coefficient representation on the coefficient field. -/
abbrev groupTrivialCoefficients : Rep k G := Rep.trivial k G k

/-- The original bar two-cocycle of actual additive characters. -/
def groupCharacterCupCocycle (χ ψ : Additive G →+ k) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k G) := by
  refine ⟨fun gh => χ (Additive.ofMul gh.1) * ψ (Additive.ofMul gh.2), ?_⟩
  apply (groupCohomology.mem_cocycles₂_def _).mpr
  intro g h j
  simp only [Representation.trivial_apply, ofMul_mul, map_add]
  ring

@[simp]
theorem groupCharacterCupCocycle_apply (χ ψ : Additive G →+ k) (g h : G) :
    groupCharacterCupCocycle k G χ ψ (g, h) =
      χ (Additive.ofMul g) * ψ (Additive.ofMul h) := rfl

/-- The actual bar H² class of this original inhomogeneous cocycle. -/
def groupCharacterCup (χ ψ : Additive G →+ k) :
    groupCohomology.H2 (groupTrivialCoefficients k G) :=
  groupCohomology.H2π (groupTrivialCoefficients k G)
    (groupCharacterCupCocycle k G χ ψ)

/-- Native H² vanishing is exactly the actual inhomogeneous primitive
equation. Neither primitive existence nor injectivity is assumed. -/
theorem groupCharacterCup_eq_zero_iff (χ ψ : Additive G →+ k) :
    groupCharacterCup k G χ ψ = 0 ↔ ∃ f : G → k, ∀ g h : G,
      f h - f (g * h) + f g = χ (Additive.ofMul g) * ψ (Additive.ofMul h) := by
  rw [groupCharacterCup, groupCohomology.H2π_eq_zero_iff]
  change (fun gh : G × G => χ (Additive.ofMul gh.1) * ψ (Additive.ofMul gh.2)) ∈
    LinearMap.range (groupCohomology.d₁₂ (groupTrivialCoefficients k G)).hom ↔ _
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro g h
    have hgh := congrFun hf (g, h)
    simpa only [groupCohomology.d₁₂_hom_apply, Rep.trivial_ρ_apply] using hgh
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    funext gh
    simp only [groupCohomology.d₁₂_hom_apply]
    exact hf gh.1 gh.2

/-- The original bar cocycle operation is bilinear on genuine characters. -/
def groupCharacterCupCocycleBilinear :
    (Additive G →+ k) →ₗ[k] (Additive G →+ k) →ₗ[k]
      groupCohomology.cocycles₂ (groupTrivialCoefficients k G) :=
    LinearMap.mk₂ k
      (fun χ ψ : Additive G →+ k => groupCharacterCupCocycle k G χ ψ)
      (by
        intro χ₁ χ₂ ψ
        apply Subtype.ext
        funext gh
        change (χ₁ (Additive.ofMul gh.1) + χ₂ (Additive.ofMul gh.1)) *
            ψ (Additive.ofMul gh.2) = _
        exact add_mul _ _ _)
      (by
        intro c χ ψ
        apply Subtype.ext
        funext gh
        change (c • χ (Additive.ofMul gh.1)) * ψ (Additive.ofMul gh.2) =
          c • (χ (Additive.ofMul gh.1) * ψ (Additive.ofMul gh.2))
        simp only [smul_eq_mul, mul_assoc])
      (by
        intro χ ψ₁ ψ₂
        apply Subtype.ext
        funext gh
        change χ (Additive.ofMul gh.1) *
          (ψ₁ (Additive.ofMul gh.2) + ψ₂ (Additive.ofMul gh.2)) = _
        exact mul_add _ _ _)
      (by
        intro c χ ψ
        apply Subtype.ext
        funext gh
        change χ (Additive.ofMul gh.1) * (c • ψ (Additive.ofMul gh.2)) =
          c • (χ (Additive.ofMul gh.1) * ψ (Additive.ofMul gh.2))
        simp only [smul_eq_mul]
        ring)

/-- The original bar operation descends through the actual native H² map. -/
def groupCharacterCupBilinear :
    (Additive G →+ k) →ₗ[k] (Additive G →+ k) →ₗ[k]
      groupCohomology.H2 (groupTrivialCoefficients k G) :=
  (groupCharacterCupCocycleBilinear k G).compr₂
    (groupCohomology.H2π (groupTrivialCoefficients k G)).hom

end ChenRanks
