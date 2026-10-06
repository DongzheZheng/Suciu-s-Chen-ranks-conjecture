import ChenRanks.BasedFundamentalGroupoidTransport
import ChenRanks.SingularFirstCohomologyCharacters
import ChenRanks.SingularTrianglePathHomotopy

/-!
# Constructing actual singular cocycles from actual group characters

Chosen original paths transport every genuine geometric edge into the
actual based group. Character values on these actual edges define a
native singular cochain. The original simplex's genuine edge homotopy
and the actual groupoid composition identity prove its native closure.
Evaluation on actual based loops then proves the inverse to the original
H¹ character map. No classifying map or H¹ correspondence is assumed.
-/

noncomputable section

open unitInterval CategoryTheory AlgebraicTopology

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
variable (k : Type) [Field k]

/-- Treat a genuine continuous path as a native path at its actual endpoints. -/
def continuousPathAtEndpoints (γ : C(I, X)) : Path (γ 0) (γ 1) := ⟨γ, rfl, rfl⟩

private theorem basedPathCharacterValue_ext (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k)
    {x y x' y' : X} (p : Path x y) (q : Path x' y') (hpq : ∀ t, p t = q t) :
    ChenRanks.basedPathCharacterValue X k base χ p =
      ChenRanks.basedPathCharacterValue X k base χ q := by
  obtain rfl : x = x' := p.source.symm.trans ((hpq 0).trans q.source)
  obtain rfl : y = y' := p.target.symm.trans ((hpq 1).trans q.target)
  have h : p = q := by ext t; exact hpq t
  rw [h]

/-- Character evaluation on a genuine continuous path with its actual endpoints. -/
def characterContinuousPathValue (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) (γ : C(I, X)) : k :=
  ChenRanks.basedPathCharacterValue X k base χ (continuousPathAtEndpoints X γ)

theorem characterContinuousPathValue_path (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) {x y : X} (p : Path x y) :
    characterContinuousPathValue X k base χ p.toContinuousMap =
      ChenRanks.basedPathCharacterValue X k base χ p := by
  apply basedPathCharacterValue_ext
  intro t
  rfl

/-- The original triangle's actual edge homotopy proves character additivity. -/
theorem characterContinuousPathValue_triangle (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k)
    (s : C(stdSimplex ℝ (Fin 3), X)) :
    characterContinuousPathValue X k base χ (s.comp (realTriangleFacePath 1)) =
      characterContinuousPathValue X k base χ (s.comp (realTriangleFacePath 2)) +
        characterContinuousPathValue X k base χ (s.comp (realTriangleFacePath 0)) := by
  change characterContinuousPathValue X k base χ (triangleDiagonalEdgePath s).toContinuousMap =
    characterContinuousPathValue X k base χ (triangleFirstEdgePath s).toContinuousMap +
      characterContinuousPathValue X k base χ (triangleSecondEdgePath s).toContinuousMap
  rw [characterContinuousPathValue_path, characterContinuousPathValue_path,
    characterContinuousPathValue_path]
  have hh := ChenRanks.basedPathCharacterValue_eq_of_homotopic X k base χ
    (Path.Homotopic.symm ⟨triangleEdgeConcatenationHomotopy s⟩)
  exact hh.trans (ChenRanks.basedPathCharacterValue_trans X k base χ
    (triangleFirstEdgePath s) (triangleSecondEdgePath s))

/-- A native singular one-cochain with genuine transported edge values. -/
def characterOneCochain (base : X) (χ : Additive (FundamentalGroup X base) →+ k) :
    cochains k X 1 :=
  ofValues k X 1 (fun s => characterContinuousPathValue X k base χ (geometricSimplexPath X s))

theorem characterOneCochain_path_value (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) {x y : X} (p : Path x y) :
    values k X 1 (characterOneCochain X k base χ) (simplexOfPath X p.toContinuousMap) =
      ChenRanks.basedPathCharacterValue X k base χ p := by
  simp only [characterOneCochain, values_ofValues,
    geometricSimplexPath_simplexOfPath]
  exact characterContinuousPathValue_path X k base χ p

/-- Native closure is proved on every genuine singular triangle. -/
theorem differential_characterOneCochain (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) :
    differential k X 1 (characterOneCochain X k base χ) = 0 := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (differential k X 1 (characterOneCochain X k base χ)) s =
    values k X 2 0 s
  rw [values_differential_one]
  simp only [characterOneCochain, values_ofValues,
    geometricSimplexPath_edge, map_zero, Pi.zero_apply]
  have h := characterContinuousPathValue_triangle X k base χ (geometricSimplex X 2 s)
  linear_combination -h

/-- The constructed closed native cochain determines an actual singular H¹ class. -/
def characterFirstCohomologyClass (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) : cohomology k X 1 :=
  cocycleClass k X 1 (toCocycle k X 1 (characterOneCochain X k base χ)
    (differential_characterOneCochain X k base χ))

/-- Its actual based-loop character is precisely the original input character. -/
theorem firstCohomologyToCharacters_characterClass (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) :
    firstCohomologyToCharacters X k base (characterFirstCohomologyClass X k base χ) = χ := by
  apply AddMonoidHom.ext
  intro g
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    change firstCohomologyCharacter X k base (characterFirstCohomologyClass X k base χ)
        (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) =
      χ (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)))
    rw [firstCohomologyCharacter_mk]
    simp only [characterFirstCohomologyClass, closedPathEvaluation_cocycleClass,
      cocycleCochain_toCocycle, characterOneCochain_path_value,
      ChenRanks.basedPathCharacterValue, ChenRanks.basedFundamentalPath_loop]

/-- Every actual additive character comes from the constructed native singular class. -/
theorem firstCohomologyToCharacters_surjective (base : X) :
    Function.Surjective (firstCohomologyToCharacters X k base) := by
  intro χ
  exact ⟨characterFirstCohomologyClass X k base χ,
    firstCohomologyToCharacters_characterClass X k base χ⟩

/-- The genuine degree-one space-to-group-character correspondence,
with inverse existence proved from actual singular simplex geometry. -/
def firstCohomologyCharactersEquiv (base : X) :
    cohomology k X 1 ≃ₗ[k] (Additive (FundamentalGroup X base) →+ k) :=
  LinearEquiv.ofBijective (firstCohomologyToCharacters X k base)
    ⟨firstCohomologyToCharacters_injective X k base,
      firstCohomologyToCharacters_surjective X k base⟩

end ChenRanks.SingularCohomology
