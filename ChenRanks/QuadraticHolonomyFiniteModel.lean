import ChenRanks.KoszulMetabelianFiniteTruncation
import ChenRanks.KoszulQuadraticMetabelianEquivalence
import ChenRanks.QuadraticHolonomyGeneratorBracket

/-!
# Actual holonomy maps to the actual finite Koszul truncations

The native quadratic holonomy quotient maps through the actual native
metabelian free quotient and its proved actual Koszul model equivalence.
The final map is the native finite-tail quotient projection. Its original
generator formula and surjectivity are proved from those actual maps.
No formality, monodromy or group comparison is an input or conclusion.
-/

noncomputable section

namespace ChenRanks.LieComparison

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [Module k V]
variable {ι : Type*} [Fintype ι] (b : _root_.Module.Basis ι k V)
variable (K : Submodule k (⋀[k]^2 V))

/-- The actual full quadratic holonomy algebra maps to the proved
original metabelian Koszul model using only actual native quotient maps. -/
def quadraticHolonomyToKoszulModel :
    QuadraticHolonomyLie k V b K →ₗ⁅k⁆ Koszul.MetabelianLieModel k V K :=
  (quadraticMetabelianToKoszulModel k V b K).comp
    (holonomyToQuadraticMetabelian k V b K)

omit [Fintype ι] in
theorem quadraticHolonomyToKoszulModel_projection (x : FreeLieAlgebra k ι) :
    quadraticHolonomyToKoszulModel k V b K (quadraticHolonomyProjection k V b K x) =
      freeLieToKoszulModel k V b K x := by
  change quadraticMetabelianToKoszulModelLinear k V b K
      (holonomyToQuadraticMetabelianLinear k V b K
        (quadraticHolonomyProjection k V b K x)) = _
  rw [holonomyToQuadraticMetabelianLinear_projection,
    quadraticMetabelianToKoszulModelLinear_projection]

/-- Original vector generators map to their actual original model coordinate. -/
theorem quadraticHolonomyToKoszulModel_generator (u : V) :
    quadraticHolonomyToKoszulModel k V b K (quadraticHolonomyGenerators k V b K u) =
      Koszul.MetabelianLieModel.generatorInclusion k V K u := by
  change quadraticHolonomyToKoszulModel k V b K
    (quadraticHolonomyProjection k V b K (freeVectorGenerators k V b u)) = _
  rw [quadraticHolonomyToKoszulModel_projection, freeLieToKoszulModel_generator]

variable [CharZero k]

theorem quadraticHolonomyToKoszulModel_surjective :
    Function.Surjective (quadraticHolonomyToKoszulModel k V b K) := by
  letI : FiniteDimensional k V := _root_.Module.Finite.of_basis b
  intro x
  obtain ⟨y, hy⟩ := (quadraticMetabelianKoszulLieEquiv k V b K).surjective x
  obtain ⟨z, rfl⟩ := quadraticMetabelianProjection_surjective k V b K y
  refine ⟨quadraticHolonomyProjection k V b K z, ?_⟩
  rw [quadraticHolonomyToKoszulModel_projection]
  change quadraticMetabelianToKoszulModelLinear k V b K
    (quadraticMetabelianProjection k V b K z) = x at hy
  rw [quadraticMetabelianToKoszulModelLinear_projection] at hy
  exact hy

omit [CharZero k] in
/-- The true native holonomy-to-finite-truncation morphism. -/
def quadraticHolonomyToFiniteModel (c : ℕ) :
    QuadraticHolonomyLie k V b K →ₗ⁅k⁆ Koszul.finiteModelTruncation k V b K c :=
  (Koszul.finiteModelProjection k V b K c).comp
    (quadraticHolonomyToKoszulModel k V b K)

omit [CharZero k] in
theorem quadraticHolonomyToFiniteModel_generator (c : ℕ) (u : V) :
    quadraticHolonomyToFiniteModel k V b K c (quadraticHolonomyGenerators k V b K u) =
      Koszul.finiteModelProjection k V b K c
        (Koszul.MetabelianLieModel.generatorInclusion k V K u) := by
  change Koszul.finiteModelProjection k V b K c
    (quadraticHolonomyToKoszulModel k V b K (quadraticHolonomyGenerators k V b K u)) = _
  rw [quadraticHolonomyToKoszulModel_generator]

theorem quadraticHolonomyToFiniteModel_surjective (c : ℕ) :
    Function.Surjective (quadraticHolonomyToFiniteModel k V b K c) :=
  (Koszul.finiteModelProjection_surjective k V b K c).comp
    (quadraticHolonomyToKoszulModel_surjective k V b K)

end ChenRanks.LieComparison
