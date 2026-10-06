import ChenRanks.GroupBarSingularInjection
import ChenRanks.SingularFirstGroupCohomology
import ChenRanks.SingularCupAlternation
import ChenRanks.ExteriorSeparationLinearEquiv
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual first-cohomology equivalence and quadratic cup-kernel comparison

All objects are the existing singular cohomology and the pinned native
bar cohomology of the original FundamentalGroup. The actual H² quotient
map and its proved surjectivity descend the actual bar pullback. Its
injectivity follows from the explicitly constructed bar primitive.
The original degree-one character equivalence and the two inverse-edge
signs give genuine cup compatibility, hence equality of the actual
exterior-square kernels under the genuine H¹ equivalence.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
variable (k : Type) [Field k]

/-- The actual degree-one singular/bar correspondence is a genuine
linear equivalence, with its inverse constructed on actual edges. -/
def firstSingularGroupH1Equiv (base : X) :
    cohomology k X 1 ≃ₗ[k] basedFundamentalGroupH1 X k base :=
  (firstCohomologyCharactersEquiv X k base).trans
    (basedFundamentalGroupH1CharactersEquiv X k base).symm

theorem firstSingularGroupH1Equiv_apply (base : X) (a : cohomology k X 1) :
    firstSingularGroupH1Equiv X k base a = firstSingularCohomologyToGroupH1 X k base a := rfl

/-- The actual native H² of the same original based group. -/
abbrev basedFundamentalGroupH2 (base : X) :=
  groupCohomology.H2 (groupTrivialCoefficients k (FundamentalGroup X base))

/-- The actual singular cocycle pullback is linear in the original bar cocycle. -/
def barTwoSingularCocycleLinear (base : X) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k (FundamentalGroup X base)) →ₗ[k]
      cocycles k X 2 where
  toFun := barTwoSingularCocycle X k base
  map_add' f g := by
    apply Subtype.ext
    change barTwoSingularCochain X k base (f + g) =
      barTwoSingularCochain X k base f + barTwoSingularCochain X k base g
    apply cochain_ext k X 2
    intro s
    change values k X 2 (barTwoSingularCochain X k base (f + g)) s =
      values k X 2 (barTwoSingularCochain X k base f + barTwoSingularCochain X k base g) s
    simp only [barTwoSingularCochain, values_ofValues, map_add, Pi.add_apply]
  map_smul' c f := by
    apply Subtype.ext
    change barTwoSingularCochain X k base (c • f) = c • barTwoSingularCochain X k base f
    apply cochain_ext k X 2
    intro s
    change values k X 2 (barTwoSingularCochain X k base (c • f)) s =
      values k X 2 (c • barTwoSingularCochain X k base f) s
    simp only [barTwoSingularCochain, values_ofValues, map_smul, Pi.smul_apply]

def barTwoSingularClassLinear (base : X) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k (FundamentalGroup X base)) →ₗ[k]
      cohomology k X 2 :=
  (cocycleClass k X 2).comp (barTwoSingularCocycleLinear X k base)

omit [PathConnectedSpace X] in
theorem actualBarH2Pi_surjective (base : X) :
    Function.Surjective
      (groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base))).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem actualBarH2Pi_ker_le_pullback_ker (base : X) :
    LinearMap.ker
        (groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base))).hom ≤
      LinearMap.ker (barTwoSingularClassLinear X k base) := by
  intro f hf
  exact (barTwoSingularCocycle_class_zero_iff X k base f).mpr hf

/-- The genuine map from original native bar H² to original singular H².
The quotient here is the actual kernel of the actual native H2π map. -/
def actualGroupH2ToSingularH2 (base : X) :
    basedFundamentalGroupH2 X k base →ₗ[k] cohomology k X 2 :=
  ((LinearMap.ker
      (groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base))).hom).liftQ
    (barTwoSingularClassLinear X k base) (actualBarH2Pi_ker_le_pullback_ker X k base)).comp
      ((groupCohomology.H2π
        (groupTrivialCoefficients k (FundamentalGroup X base))).hom.quotKerEquivOfSurjective
          (actualBarH2Pi_surjective X k base)).symm.toLinearMap

theorem actualGroupH2ToSingularH2_pi (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base))) :
    actualGroupH2ToSingularH2 X k base
        (groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base)) f) =
      cocycleClass k X 2 (barTwoSingularCocycle X k base f) := by
  change actualGroupH2ToSingularH2 X k base
    ((groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base))).hom f) = _
  unfold actualGroupH2ToSingularH2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.liftQ_apply, barTwoSingularClassLinear, barTwoSingularCocycleLinear]
  rfl

/-- Actual injectivity is proved by the actual loop primitive construction. -/
theorem actualGroupH2ToSingularH2_injective (base : X) :
    Function.Injective (actualGroupH2ToSingularH2 X k base) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hz : actualGroupH2ToSingularH2 X k base (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨f, hf⟩ := actualBarH2Pi_surjective X k base (a - b)
  rw [← hf, actualGroupH2ToSingularH2_pi] at hz
  exact hf ▸ (barTwoSingularCocycle_class_zero_iff X k base f).mp hz

private theorem inverseTransportedSingularEdge_character (base : X)
    (χ : Additive (FundamentalGroup X base) →+ k) (s : simplices X 1) :
    χ (Additive.ofMul (inverseTransportedSingularEdge X base s)) =
      -values k X 1 (characterOneCochain X k base χ) s := by
  simp only [characterOneCochain, values_ofValues, inverseTransportedSingularEdge,
    inverseTransportedContinuousPath, characterContinuousPathValue,
    basedPathCharacterValue]
  change χ (-Additive.ofMul (basedFundamentalPath X base
    (continuousPathAtEndpoints X (geometricSimplexPath X s)))) = _
  rw [map_neg]

theorem barCharacterCup_singular_cochain (base : X)
    (χ ψ : Additive (FundamentalGroup X base) →+ k) :
    barTwoSingularCochain X k base
        (groupCharacterCupCocycle k (FundamentalGroup X base) χ ψ) =
      cupOne k X (characterOneCochain X k base χ) (characterOneCochain X k base ψ) := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (barTwoSingularCochain X k base
      (groupCharacterCupCocycle k (FundamentalGroup X base) χ ψ)) s =
    values k X 2 (cupOne k X (characterOneCochain X k base χ)
      (characterOneCochain X k base ψ)) s
  simp only [barTwoSingularCochain, values_ofValues, groupCharacterCupCocycle_apply,
    values_cupOne, inverseTransportedSingularEdge_character, neg_mul_neg]

/-- The true bar cup pulls back to the true singular cup: the two
actual inverse-edge signs cancel, rather than being dropped. -/
theorem actualGroupH2ToSingularH2_characterCup (base : X)
    (χ ψ : Additive (FundamentalGroup X base) →+ k) :
    actualGroupH2ToSingularH2 X k base
        (groupCharacterCup k (FundamentalGroup X base) χ ψ) =
      cup k X (characterFirstCohomologyClass X k base χ)
        (characterFirstCohomologyClass X k base ψ) := by
  rw [groupCharacterCup, actualGroupH2ToSingularH2_pi]
  unfold characterFirstCohomologyClass
  rw [cup_cocycleClass]
  apply congrArg (cocycleClass k X 2)
  apply Subtype.ext
  exact barCharacterCup_singular_cochain X k base χ ψ

/-- The degree-one operation on the original native group H¹ objects
is the original inhomogeneous bar product on their actual characters. -/
def actualBasedGroupCup (base : X) :
    basedFundamentalGroupH1 X k base →ₗ[k] basedFundamentalGroupH1 X k base →ₗ[k]
      basedFundamentalGroupH2 X k base :=
  (groupCharacterCupBilinear k (FundamentalGroup X base)).compl₁₂
    (basedFundamentalGroupH1CharactersEquiv X k base).toLinearMap
    (basedFundamentalGroupH1CharactersEquiv X k base).toLinearMap

theorem actualGroupH2ToSingularH2_cup (base : X) (a b : cohomology k X 1) :
    actualGroupH2ToSingularH2 X k base
        (actualBasedGroupCup X k base (firstSingularGroupH1Equiv X k base a)
          (firstSingularGroupH1Equiv X k base b)) = cup k X a b := by
  have ha : characterFirstCohomologyClass X k base (firstCohomologyToCharacters X k base a) = a := by
    apply firstCohomologyToCharacters_injective X k base
    rw [firstCohomologyToCharacters_characterClass]
  have hb : characterFirstCohomologyClass X k base (firstCohomologyToCharacters X k base b) = b := by
    apply firstCohomologyToCharacters_injective X k base
    rw [firstCohomologyToCharacters_characterClass]
  change actualGroupH2ToSingularH2 X k base
      (groupCharacterCup k (FundamentalGroup X base)
        ((basedFundamentalGroupH1CharactersEquiv X k base)
          ((basedFundamentalGroupH1CharactersEquiv X k base).symm
            (firstCohomologyToCharacters X k base a)))
        ((basedFundamentalGroupH1CharactersEquiv X k base)
          ((basedFundamentalGroupH1CharactersEquiv X k base).symm
            (firstCohomologyToCharacters X k base b)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    actualGroupH2ToSingularH2_characterCup, ha, hb]

variable [CharZero k]

theorem actualBasedGroupCup_self (base : X) (a : basedFundamentalGroupH1 X k base) :
    actualBasedGroupCup X k base a a = 0 := by
  obtain ⟨b, rfl⟩ := (firstSingularGroupH1Equiv X k base).surjective a
  apply actualGroupH2ToSingularH2_injective X k base
  rw [actualGroupH2ToSingularH2_cup, map_zero, cup_self_eq_zero]

/-- Alternation in the actual native group H¹ is derived from actual
bar injection and actual singular alternation. -/
def actualBasedGroupAlternatingCup (base : X) :
    (basedFundamentalGroupH1 X k base) [⋀^Fin 2]→ₗ[k]
      (basedFundamentalGroupH2 X k base) where
  toFun a := actualBasedGroupCup X k base (a 0) (a 1)
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change actualBasedGroupCup X k base (a 0) (a 1) = 0
      rw [h]
      exact actualBasedGroupCup_self X k base (a 1)
    · change a 1 = a 0 at h
      change actualBasedGroupCup X k base (a 0) (a 1) = 0
      rw [h]
      exact actualBasedGroupCup_self X k base (a 0)
    · exact (hij rfl).elim

def actualBasedGroupQuadraticCup (base : X) :
    (⋀[k]^2 (basedFundamentalGroupH1 X k base)) →ₗ[k] basedFundamentalGroupH2 X k base :=
  exteriorPower.alternatingMapLinearEquiv (actualBasedGroupAlternatingCup X k base)

theorem actualBasedGroupQuadraticCup_exteriorWedge (base : X)
    (a b : basedFundamentalGroupH1 X k base) :
    actualBasedGroupQuadraticCup X k base (exteriorWedge (k := k) a b) =
      actualBasedGroupCup X k base a b := by
  simp [actualBasedGroupQuadraticCup, exteriorWedge, actualBasedGroupAlternatingCup]

/-- A literal equality of the actual exterior-square linear maps. -/
theorem actualGroup_quadraticCup_comparison (base : X) :
    (actualGroupH2ToSingularH2 X k base).comp
        ((actualBasedGroupQuadraticCup X k base).comp
          (exteriorPower.map 2 (firstSingularGroupH1Equiv X k base).toLinearMap)) =
      quadraticCup k X := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : exteriorPower.ιMulti k 2 v = exteriorWedge (v 0) (v 1) := by
    change exteriorPower.ιMulti k 2 v = exteriorPower.ιMulti k 2 ![v 0, v 1]
    congr 1
    funext i
    fin_cases i <;> rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, hv,
    exteriorPowerMap_exteriorWedge, actualBasedGroupQuadraticCup_exteriorWedge,
    quadraticCup_exteriorWedge]
  exact actualGroupH2ToSingularH2_cup X k base (v 0) (v 1)

/-- The actual group quadratic kernel pulls back to the original
singular quadratic kernel along the genuine H¹ equivalence. -/
theorem actualGroup_quadraticCup_kernel_comparison (base : X) :
    (LinearMap.ker (actualBasedGroupQuadraticCup X k base)).comap
        (exteriorPower.map 2 (firstSingularGroupH1Equiv X k base).toLinearMap) =
      quadraticCupKernel k X := by
  ext z
  change actualBasedGroupQuadraticCup X k base
      (exteriorPower.map 2 (firstSingularGroupH1Equiv X k base).toLinearMap z) = 0 ↔
    quadraticCup k X z = 0
  have hz := congrArg (fun f => f z) (actualGroup_quadraticCup_comparison X k base)
  change actualGroupH2ToSingularH2 X k base
    (actualBasedGroupQuadraticCup X k base
      (exteriorPower.map 2 (firstSingularGroupH1Equiv X k base).toLinearMap z)) =
        quadraticCup k X z at hz
  rw [← hz]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply actualGroupH2ToSingularH2_injective X k base
    simpa only [map_zero] using h

end ChenRanks.SingularCohomology
