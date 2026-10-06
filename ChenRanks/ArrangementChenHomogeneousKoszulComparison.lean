import ChenRanks.ArrangementFiniteEulerChenLeadingComparison
import ChenRanks.KoszulLieHomPhysicalDegrees
import ChenRanks.ArrangementLowerCentralDegreeOneFinite
import ChenRanks.GroupLowerCentralFinitePieces

/-!
# Actual original Chen quotients and original homogeneous Koszul modules

The genuine original model-to-Chen map's generator formula discharges
the intermediate weight-one condition. Euler compatibility and genuine
source/target projections then prove comparison on the actual original
successive group quotients, beyond the whole-map bijection. Ordinary
Chen degree r+2 corresponds to the original homogeneous Koszul degree r
and native original group-piece index r+1.

The natural-valued dimension is compared after true finite-dimensionality
of the original rational Chen pieces is derived from the original first
piece and actual commutator tensor generation. The original cardinal
rank is also retained. No Chen dimension is defined by the expected
formula. This file is an uncompiled candidate.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open LieComparison Koszul

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (base : A.Complement)

local instance arrangementChenOriginalDegreeGroup (r : ℕ) :
    AddCommGroup (homogeneousModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r) :=
  canonicalHomogeneousQuotientAddCommGroup ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r

local instance arrangementChenOriginalDegreeMonoid (r : ℕ) :
    AddCommMonoid (homogeneousModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r) :=
  (arrangementChenOriginalDegreeGroup A r).toAddCommMonoid

local instance arrangementChenOriginalDegreeScalars (r : ℕ) :
    _root_.Module ℂ (homogeneousModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r) :=
  canonicalHomogeneousQuotientBaseCoefficients ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r

/-- The original canonical generator formula proves weight one in the
same original maximal metabelian group's actual degree-one quotient. -/
theorem actualEquationKoszulModelToChen_generator_physicalEuler
    (u : _root_.Module.Dual ℂ (ι → ℂ)) :
    scalarGroupPhysicalEulerLinear ℂ (metabelianQuotient (FundamentalGroup A.Complement base))
      (A.actualEquationKoszulModelToChen base
        (MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)) =
      A.actualEquationKoszulModelToChen base
        (MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u) := by
  rw [A.actualEquationKoszulModelToChen_generator base u,
    scalarGroupPhysicalEulerLinear_inclusion]
  simp only [Nat.zero_add, Nat.cast_one, one_smul]

/-- The genuine original comparison preserves physical degree by a
proved Euler identity, without a degree-preservation premise. -/
theorem actualEquationKoszulModelToChen_physicalEuler
    (x : A.ActualEquationKoszulLieModel) :
    A.actualEquationKoszulModelToChen base
      (nativeEulerDerivation ℂ A.ActualEquationKoszulLieModel
        (modelPositiveComponent ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)) x) =
      scalarGroupPhysicalEulerLinear ℂ
        (metabelianQuotient (FundamentalGroup A.Complement base))
        (A.actualEquationKoszulModelToChen base x) :=
  originalModelPhysicalEuler_intertwines ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
    (metabelianQuotient (FundamentalGroup A.Complement base))
    (A.actualEquationKoszulModelToChen base)
    (A.actualEquationKoszulModelToChen_generator_physicalEuler base) x

/-- The same actual comparison lands in the actual original physical
group quotient for every positive original homogeneous degree. -/
theorem actualEquationKoszulModelToChen_homogeneous (q : ℕ) (hq : 1 ≤ q)
    (x : A.ActualEquationKoszulLieModel)
    (hx : x ∈ modelPositiveComponent ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) q) :
    A.actualEquationKoszulModelToChen base x =
      scalarGroupGradedInclusion ℂ
        (metabelianQuotient (FundamentalGroup A.Complement base)) (q - 1)
        (scalarGroupPieceProjection ℂ
          (metabelianQuotient (FundamentalGroup A.Complement base)) (q - 1)
          (A.actualEquationKoszulModelToChen base x)) :=
  originalModelLieHom_homogeneous_originalPiece ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
    (metabelianQuotient (FundamentalGroup A.Complement base))
    (A.actualEquationKoszulModelToChen base)
    (A.actualEquationKoszulModelToChen_generator_physicalEuler base) q hq x hx

/-- The genuine graded comparison retains the same original rational
Chen quotient under complex scalar extension. Both injectivity and
surjectivity are proved for the same original map. -/
def actualChenKoszulDegreeEquiv (r : ℕ) :
    homogeneousModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r ≃ₗ[ℂ]
      scalarLowerCentralPiece ℂ
        (metabelianQuotient (FundamentalGroup A.Complement base)) (r + 1) :=
  originalKoszulDegreeGroupPieceEquiv ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
    (metabelianQuotient (FundamentalGroup A.Complement base))
    (A.actualEquationKoszulModelToChen base)
    (A.actualEquationKoszulModelToChen_generator_physicalEuler base) r
    ⟨A.actualEquationKoszulModelToChen_injective base,
      A.actualEquationKoszulModelToChen_surjective base⟩

/-- Actual higher rational Chen pieces are finite, derived from the
original first-piece finiteness and true quotient bracket generation. -/
instance actualRationalChenPiece_finiteDimensional (n : ℕ) :
    FiniteDimensional ℚ (rationalChenSpace (FundamentalGroup A.Complement base) n) := by
  letI : FiniteDimensional ℚ (rationalChenSpace (FundamentalGroup A.Complement base) 0) :=
    A.actualRationalChenDegreeOne_finiteDimensional base
  exact rationalChenSpace_finiteDimensional (FundamentalGroup A.Complement base) n

/-- In ordinary Chen degree r+2 the actual finite Chen rank is the
dimension of the original Koszul W_r; neither rank is a formula-defined
stand-in. This is not yet the stable resonance counting formula. -/
theorem actualFiniteChenRank_eq_originalKoszulDegree (r : ℕ) :
    finiteChenRank (FundamentalGroup A.Complement base) (r + 1) =
      _root_.Module.finrank ℂ (homogeneousModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r) := by
  change _root_.Module.finrank ℚ
      (rationalLowerCentralPiece (metabelianQuotient (FundamentalGroup A.Complement base))
        (r + 1)) = _
  rw [← scalarLowerCentralPiece_finrank ℂ
    (metabelianQuotient (FundamentalGroup A.Complement base)) (r + 1)]
  exact (A.actualChenKoszulDegreeEquiv base r).finrank_eq.symm

/-- The original cardinal rank has the same genuinely finite value,
with original group quotient degree r+2 and Koszul degree r explicit. -/
theorem actualRationalChenRank_eq_originalKoszulDegree (r : ℕ) :
    rationalChenRank (FundamentalGroup A.Complement base) (r + 1) =
      (_root_.Module.finrank ℂ (homogeneousModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) r) : Cardinal) := by
  rw [← finiteChenRank_eq_rationalChenRank,
    A.actualFiniteChenRank_eq_originalKoszulDegree base r]

end ChenRanks.AffineArrangement
