import ChenRanks.ArrangementEquationHolonomyRelations
import ChenRanks.ArrangementLogarithmicHolonomyCurvature
import ChenRanks.ScalarHolonomyChenComparison
import ChenRanks.ScalarChenDegreeOne

/-!
# The original equation-dual Koszul model maps to the same original Chen Lie

The source relation space is exactly the paper's determinant annihilator
of its original rational quadratic kernel. The original equation-dual
map identifies its generator vectors with the same fundamental group's
actual first lower-central quotient. The proved original group cup
calculation kills these original quadratic relations. Genuine quotient
universal properties construct a surjective native holonomy map, then
its original metabelian quotient and its actual Koszul Lie model map to
the same original group's actual scalar Chen Lie algebra.

No formality, quadratic relation vanishing, comparison map, injectivity,
degree-preservation field or dimension formula is supplied. The explicit
generator formula retains the original ordinary degree one. Higher
injectivity and the final Chen comparison remain separate steps.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (base : A.Complement)

local instance equationHolonomyChenPathConnected : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations

/-- The paper's original dual basis, transported by the actual original
cotangent/first-quotient equivalence. -/
def actualEquationScalarFirstBasis :
    _root_.Module.Basis (Fin (_root_.Module.finrank ℂ (ι → ℂ))) ℂ
      (scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0) :=
  A.actualLogHolonomyLabelBasis.dualBasis.map (A.actualEquationDualScalarFirst ℂ base)

/-- The actual free map uses the original basis index set, with its
actual transported first-quotient vectors. -/
def actualEquationFreeLieToGroupGraded :
    FreeLieAlgebra ℂ (Fin (_root_.Module.finrank ℂ (ι → ℂ))) →ₗ⁅ℂ⁆
      scalarGroupAssociatedGraded ℂ (FundamentalGroup A.Complement base) :=
  scalarGroupAssociatedGradedFreeLift ℂ (FundamentalGroup A.Complement base)
    (A.actualEquationScalarFirstBasis base)

theorem actualEquationFreeLieToGroupGraded_generator
    (u : _root_.Module.Dual ℂ (ι → ℂ)) :
    A.actualEquationFreeLieToGroupGraded base
      (freeVectorGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis u) =
      scalarGroupGradedInclusion ℂ (FundamentalGroup A.Complement base) 0
        (A.actualEquationDualScalarFirst ℂ base u) := by
  have h : (A.actualEquationFreeLieToGroupGraded base).toLinearMap.comp
      (freeVectorGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis) =
      (scalarGroupGradedInclusion ℂ (FundamentalGroup A.Complement base) 0).comp
        (A.actualEquationDualScalarFirst ℂ base).toLinearMap := by
    apply A.actualLogHolonomyLabelBasis.dualBasis.ext
    intro i
    simp only [LinearMap.comp_apply, freeVectorGenerators_basis]
    exact scalarGroupAssociatedGradedFreeLift_generator ℂ
      (FundamentalGroup A.Complement base) (A.actualEquationScalarFirstBasis base) i
  exact LinearMap.congr_fun h u

/-- Original exterior generator brackets pass through the actual
equation-dual map, into the original second group quotient. -/
theorem actualEquationFreeLieToGroupGraded_generatorBracket :
    (A.actualEquationFreeLieToGroupGraded base).toLinearMap.comp
      (freeGeneratorBracket ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis) =
    (scalarGroupGradedInclusion ℂ (FundamentalGroup A.Complement base) 1).comp
      ((scalarFirstExteriorBracket ℂ (FundamentalGroup A.Complement base)).comp
        (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap)) := by
  apply exteriorPower.linearMap_ext
  apply DFunLike.ext
  intro a
  have ha : exteriorPower.ιMulti ℂ 2 a = exteriorWedge (k := ℂ) (a 0) (a 1) := by
    change exteriorPower.ιMulti ℂ 2 a = exteriorPower.ιMulti ℂ 2 ![a 0, a 1]
    congr 1
    funext i
    fin_cases i <;> rfl
  change A.actualEquationFreeLieToGroupGraded base
      (freeGeneratorBracket ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis (exteriorPower.ιMulti ℂ 2 a)) =
    scalarGroupGradedInclusion ℂ (FundamentalGroup A.Complement base) 1
      (scalarFirstExteriorBracket ℂ (FundamentalGroup A.Complement base)
        (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap
          (exteriorPower.ιMulti ℂ 2 a)))
  rw [ha, freeGeneratorBracket_exteriorWedge, LieHom.map_lie,
    actualEquationFreeLieToGroupGraded_generator,
    actualEquationFreeLieToGroupGraded_generator,
    exteriorPowerMap_exteriorWedge, scalarFirstExteriorBracket_wedge]
  exact scalarGroupAssociatedGraded_lie_inclusions ℂ
    (FundamentalGroup A.Complement base) 0 0
      (A.actualEquationDualScalarFirst ℂ base (a 0))
      (A.actualEquationDualScalarFirst ℂ base (a 1))

/-- The original paper relation ideal is killed by the actual free map,
using the already proved original group cup calculation. -/
theorem actualEquationQuadraticIdeal_le_groupFreeMap_ker :
    quadraticRelationIdeal ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) ≤
      (A.actualEquationFreeLieToGroupGraded base).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro x ⟨w, rfl⟩
  change A.actualEquationFreeLieToGroupGraded base
    (freeGeneratorBracket ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis (w : _)) = 0
  have h := LinearMap.congr_fun
    (A.actualEquationFreeLieToGroupGraded_generatorBracket base) (w : _)
  have hz := A.equationHolonomyRelations_le_originalBracketKernel base w.property
  change scalarFirstExteriorBracket ℂ (FundamentalGroup A.Complement base)
    (exteriorPower.map 2 (A.actualEquationDualScalarFirst ℂ base).toLinearMap (w : _)) = 0 at hz
  exact h.trans (by rw [LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero])

/-- Actual native descent from exactly the original paper holonomy quotient. -/
def actualEquationHolonomyToGroupLinear :
    A.ActualLogarithmicHolonomyLie →ₗ[ℂ]
      scalarGroupAssociatedGraded ℂ (FundamentalGroup A.Complement base) :=
  (quadraticRelationIdeal ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)).toSubmodule.liftQ
    (A.actualEquationFreeLieToGroupGraded base).toLinearMap
    (A.actualEquationQuadraticIdeal_le_groupFreeMap_ker base)

@[simp] theorem actualEquationHolonomyToGroupLinear_projection
    (x : FreeLieAlgebra ℂ (Fin (_root_.Module.finrank ℂ (ι → ℂ)))) :
    A.actualEquationHolonomyToGroupLinear base
      (quadraticHolonomyProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x) =
      A.actualEquationFreeLieToGroupGraded base x :=
  Submodule.liftQ_apply _ _ _

def actualEquationHolonomyToGroupGraded :
    A.ActualLogarithmicHolonomyLie →ₗ⁅ℂ⁆
      scalarGroupAssociatedGraded ℂ (FundamentalGroup A.Complement base) where
  __ := A.actualEquationHolonomyToGroupLinear base
  map_lie' := by
    intro x y
    obtain ⟨x, rfl⟩ := quadraticHolonomyProjection_surjective ℂ
      (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x
    obtain ⟨y, rfl⟩ := quadraticHolonomyProjection_surjective ℂ
      (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) y
    change A.actualEquationHolonomyToGroupLinear base ⁅_, _⁆ =
      ⁅A.actualEquationHolonomyToGroupLinear base _, A.actualEquationHolonomyToGroupLinear base _⁆
    rw [← LieHom.map_lie, actualEquationHolonomyToGroupLinear_projection,
      actualEquationHolonomyToGroupLinear_projection, actualEquationHolonomyToGroupLinear_projection]
    exact LieHom.map_lie _ x y

@[simp] theorem actualEquationHolonomyToGroupGraded_projection
    (x : FreeLieAlgebra ℂ (Fin (_root_.Module.finrank ℂ (ι → ℂ)))) :
    A.actualEquationHolonomyToGroupGraded base
      (quadraticHolonomyProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x) =
      A.actualEquationFreeLieToGroupGraded base x :=
  A.actualEquationHolonomyToGroupLinear_projection base x

theorem actualEquationHolonomyToGroupGraded_generator
    (u : _root_.Module.Dual ℂ (ι → ℂ)) :
    A.actualEquationHolonomyToGroupGraded base (A.actualLogHolonomyGeneratorMap u) =
      scalarGroupGradedInclusion ℂ (FundamentalGroup A.Complement base) 0
        (A.actualEquationDualScalarFirst ℂ base u) := by
  change A.actualEquationHolonomyToGroupGraded base
    (quadraticHolonomyProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
      (freeVectorGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis u)) = _
  rw [actualEquationHolonomyToGroupGraded_projection,
    actualEquationFreeLieToGroupGraded_generator]

/-- The transported genuine basis generates the same original group Lie
algebra, so the actual native paper holonomy map is genuinely onto. -/
theorem actualEquationHolonomyToGroupGraded_surjective :
    Function.Surjective (A.actualEquationHolonomyToGroupGraded base) := by
  intro x
  obtain ⟨y, hy⟩ := scalarGroupAssociatedGradedFreeLift_surjective ℂ
    (FundamentalGroup A.Complement base) (A.actualEquationScalarFirstBasis base) x
  exact ⟨quadraticHolonomyProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) y,
      (A.actualEquationHolonomyToGroupGraded_projection base y).trans hy⟩

/-- The target retains the original based fundamental group's actual
maximal metabelian quotient and its actual lower-central quotients. -/
def actualEquationHolonomyToChenGraded :
    A.ActualLogarithmicHolonomyLie →ₗ⁅ℂ⁆
      scalarChenAssociatedGraded ℂ (FundamentalGroup A.Complement base) :=
  (scalarGroupToChenGradedLieHom ℂ (FundamentalGroup A.Complement base)).comp
    (A.actualEquationHolonomyToGroupGraded base)

theorem actualEquationHolonomyToChenGraded_surjective :
    Function.Surjective (A.actualEquationHolonomyToChenGraded base) :=
  (scalarGroupToChenGradedLieHom_surjective ℂ (FundamentalGroup A.Complement base)).comp
    (A.actualEquationHolonomyToGroupGraded_surjective base)

theorem actualEquationHolonomyToChenGraded_generator
    (u : _root_.Module.Dual ℂ (ι → ℂ)) :
    A.actualEquationHolonomyToChenGraded base (A.actualLogHolonomyGeneratorMap u) =
      scalarGroupGradedInclusion ℂ (metabelianQuotient (FundamentalGroup A.Complement base)) 0
        (scalarFirstChenEquiv (FundamentalGroup A.Complement base) ℂ
          (A.actualEquationDualScalarFirst ℂ base u)) := by
  change scalarGroupToChenGradedLieHom ℂ (FundamentalGroup A.Complement base)
    (A.actualEquationHolonomyToGroupGraded base (A.actualLogHolonomyGeneratorMap u)) = _
  rw [actualEquationHolonomyToGroupGraded_generator,
    scalarGroupToChenGradedLieHom_first_inclusion]

theorem actualEquationHolonomySecondDerived_le_chenMap_ker :
    LieAlgebra.derivedSeries ℂ A.ActualLogarithmicHolonomyLie 2 ≤
      (A.actualEquationHolonomyToChenGraded base).ker := by
  apply LieIdeal.map_eq_bot_iff.mp
  apply le_bot_iff.mp
  have h := LieIdeal.derivedSeries_map_le (f := A.actualEquationHolonomyToChenGraded base) 2
  rw [scalarChenAssociatedGraded_second_derived_eq_bot] at h
  exact h

/-- The paper holonomy algebra's own actual metabelian quotient. -/
abbrev ActualEquationHolonomyMetabelianLie :=
  HolonomyMetabelianQuotient ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

def actualEquationHolonomyMetabelianToChenLinear :
    A.ActualEquationHolonomyMetabelianLie →ₗ[ℂ]
      scalarChenAssociatedGraded ℂ (FundamentalGroup A.Complement base) :=
  (LieAlgebra.derivedSeries ℂ A.ActualLogarithmicHolonomyLie 2).toSubmodule.liftQ
    (A.actualEquationHolonomyToChenGraded base).toLinearMap
    (A.actualEquationHolonomySecondDerived_le_chenMap_ker base)

@[simp] theorem actualEquationHolonomyMetabelianToChenLinear_projection
    (x : A.ActualLogarithmicHolonomyLie) :
    A.actualEquationHolonomyMetabelianToChenLinear base
      (holonomyMetabelianProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x) =
      A.actualEquationHolonomyToChenGraded base x :=
  Submodule.liftQ_apply _ _ _

def actualEquationHolonomyMetabelianToChen :
    A.ActualEquationHolonomyMetabelianLie →ₗ⁅ℂ⁆
      scalarChenAssociatedGraded ℂ (FundamentalGroup A.Complement base) where
  __ := A.actualEquationHolonomyMetabelianToChenLinear base
  map_lie' := by
    intro x y
    obtain ⟨x, rfl⟩ := holonomyMetabelianProjection_surjective ℂ
      (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x
    obtain ⟨y, rfl⟩ := holonomyMetabelianProjection_surjective ℂ
      (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) y
    change A.actualEquationHolonomyMetabelianToChenLinear base ⁅_, _⁆ =
      ⁅A.actualEquationHolonomyMetabelianToChenLinear base _,
        A.actualEquationHolonomyMetabelianToChenLinear base _⁆
    rw [← LieHom.map_lie, actualEquationHolonomyMetabelianToChenLinear_projection,
      actualEquationHolonomyMetabelianToChenLinear_projection,
      actualEquationHolonomyMetabelianToChenLinear_projection]
    exact LieHom.map_lie _ x y

@[simp] theorem actualEquationHolonomyMetabelianToChen_projection
    (x : A.ActualLogarithmicHolonomyLie) :
    A.actualEquationHolonomyMetabelianToChen base
      (holonomyMetabelianProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x) =
      A.actualEquationHolonomyToChenGraded base x :=
  A.actualEquationHolonomyMetabelianToChenLinear_projection base x

theorem actualEquationHolonomyMetabelianToChen_surjective :
    Function.Surjective (A.actualEquationHolonomyMetabelianToChen base) := by
  intro x
  obtain ⟨y, hy⟩ := A.actualEquationHolonomyToChenGraded_surjective base x
  exact ⟨holonomyMetabelianProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) y,
    (A.actualEquationHolonomyMetabelianToChen_projection base y).trans hy⟩

/-- The actual original paper Koszul Lie model, with the same original K. -/
abbrev ActualEquationKoszulLieModel :=
  Koszul.MetabelianLieModel ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

def actualEquationKoszulModelToChen :
    A.ActualEquationKoszulLieModel →ₗ⁅ℂ⁆
      scalarChenAssociatedGraded ℂ (FundamentalGroup A.Complement base) :=
  (A.actualEquationHolonomyMetabelianToChen base).comp
    ((holonomyMetabelianQuadraticEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)).symm.toLieHom.comp
        (quadraticMetabelianKoszulLieEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)).symm.toLieHom)

/-- This is a genuine surjection from the paper's original K to the
same original fundamental group's actual scalar Chen Lie algebra. -/
theorem actualEquationKoszulModelToChen_surjective :
    Function.Surjective (A.actualEquationKoszulModelToChen base) :=
  (A.actualEquationHolonomyMetabelianToChen_surjective base).comp
    ((holonomyMetabelianQuadraticEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)).symm.surjective.comp
        (quadraticMetabelianKoszulLieEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)).symm.surjective)

/-- The original Koszul generator lands in the same original group's
actual ordinary degree-one quotient, with the actual first Chen
equivalence retaining the original abelianization map. -/
theorem actualEquationKoszulModelToChen_generator
    (u : _root_.Module.Dual ℂ (ι → ℂ)) :
    A.actualEquationKoszulModelToChen base
      (Koszul.MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u) =
      scalarGroupGradedInclusion ℂ (metabelianQuotient (FundamentalGroup A.Complement base)) 0
        (scalarFirstChenEquiv (FundamentalGroup A.Complement base) ℂ
          (A.actualEquationDualScalarFirst ℂ base u)) := by
  let eQ := quadraticMetabelianKoszulLieEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
  let eH := holonomyMetabelianQuadraticEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
  have hQ : eQ.symm
      (Koszul.MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u) =
      quadraticMetabelianGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u := by
    apply eQ.injective
    change eQ (eQ.symm
      (Koszul.MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)) =
      eQ (quadraticMetabelianGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)
    rw [eQ.apply_symm_apply]
    exact (quadraticMetabelianToKoszulModel_generator ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u).symm
  have hH : eH.symm
      (quadraticMetabelianGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u) =
      holonomyMetabelianProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
        (A.actualLogHolonomyGeneratorMap u) := by
    apply eH.injective
    change eH (eH.symm
      (quadraticMetabelianGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)) =
      eH (holonomyMetabelianProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
        (A.actualLogHolonomyGeneratorMap u))
    rw [eH.apply_symm_apply]
    change quadraticMetabelianGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u =
      holonomyMetabelianToQuadraticLinear ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
        (holonomyMetabelianProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
          (A.actualLogHolonomyGeneratorMap u))
    rw [holonomyMetabelianToQuadraticLinear_projection]
    change quadraticMetabelianGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u =
      holonomyToQuadraticMetabelianLinear ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
        (quadraticHolonomyProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
          (freeVectorGenerators ℂ (_root_.Module.Dual ℂ (ι → ℂ))
            A.actualLogHolonomyLabelBasis.dualBasis u))
    rw [holonomyToQuadraticMetabelianLinear_projection]
    rfl
  change A.actualEquationHolonomyMetabelianToChen base
    (eH.symm (eQ.symm
      (Koszul.MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u))) = _
  rw [hQ, hH, actualEquationHolonomyMetabelianToChen_projection,
    actualEquationHolonomyToChenGraded_generator]

end ChenRanks.AffineArrangement
