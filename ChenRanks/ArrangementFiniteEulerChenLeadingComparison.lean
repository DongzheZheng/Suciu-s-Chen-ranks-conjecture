import ChenRanks.ArrangementFiniteEulerFirstClassCoordinates
import ChenRanks.ArrangementFiniteEulerChenMonodromy
import ChenRanks.ArrangementEquationHolonomyChenSurjection
import ChenRanks.NativeEulerExponentialRepresentationLeading
import ChenRanks.KoszulFiniteModelLeadingSeparation
import ChenRanks.KoszulMetabelianGeneratorExt

/-!
# Actual finite leading maps compare the original model and original Chen Lie

The finite target, its exponential subgroup, the original monodromy, and
the original maximal metabelian quotient are the previously constructed
objects. The actual first monodromy character calculation is extended
through the original integral quotient and scalar tensor product. The
original free-Lie uniqueness theorem then proves the comparison on the
entire original model, without assuming that comparison or its higher
degree injectivity. The original finite homogeneous decomposition proves
that the resulting positive-bound family separates the original model.

This file is an uncompiled candidate. Its final original-model injection
depends on the actual geometric monodromy/period constructions through
their stated parent theorems. No expected first identity, model map,
representation condition, comparison injection, or formality is input.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct DirectSum

namespace ChenRanks.AffineArrangement

open LieComparison Koszul

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)
variable (c : ℕ)


/-- Canonical native quotient group dictionaries, kept explicit for the
actual finite target rather than searched through its original model. -/
private abbrev comparisonRaisingPieceGroups (k E : Type*) [Field k]
    [AddCommGroup E] [_root_.Module k E] (F : ℕ → Submodule k E) :
    (i : ℕ) → AddCommGroup (DegreeRaisingPiece k E F i) :=
  fun i => Submodule.Quotient.addCommGroup (nextDegreeRaisingWithin k E F i)

private abbrev comparisonRaisingPieceModules (k E : Type*) [Field k]
    [AddCommGroup E] [_root_.Module k E] (F : ℕ → Submodule k E) :
    (i : ℕ) → _root_.Module k (DegreeRaisingPiece k E F i) :=
  fun i => Submodule.Quotient.module (nextDegreeRaisingWithin k E F i)

local instance actualComparisonPieceGroups :
    (i : ℕ) → AddCommGroup (DegreeRaisingPiece ℂ
      (A.ActualFiniteLogarithmicEulerSpace c)
      (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c)) i) :=
  comparisonRaisingPieceGroups ℂ (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))

local instance actualComparisonPieceMonoids :
    (i : ℕ) → AddCommMonoid (DegreeRaisingPiece ℂ
      (A.ActualFiniteLogarithmicEulerSpace c)
      (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c)) i) :=
  fun i => (comparisonRaisingPieceGroups ℂ (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c)) i).toAddCommMonoid

local instance actualComparisonPieceModules :
    (i : ℕ) → _root_.Module ℂ (DegreeRaisingPiece ℂ
      (A.ActualFiniteLogarithmicEulerSpace c)
      (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c)) i) :=
  comparisonRaisingPieceModules ℂ (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))

local instance actualComparisonAxisGroup :
    AddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  Submodule.Quotient.addCommGroup (nativeGradedTail ℂ
    (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c) 2)

local instance actualComparisonAxisModule :
    _root_.Module ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  Submodule.Quotient.module (nativeGradedTail ℂ
    (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c) 2)

local instance actualComparisonOriginalModelGroup :
    AddCommGroup A.ActualEquationKoszulLieModel :=
  MetabelianLieModel.modelAddCommGroup ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

local instance actualComparisonOriginalModelModule :
    _root_.Module ℂ A.ActualEquationKoszulLieModel :=
  MetabelianLieModel.modelModule ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

local instance actualComparisonOriginalModelLieRing :
    LieRing A.ActualEquationKoszulLieModel :=
  MetabelianLieModel.modelLieRing ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

local instance actualComparisonOriginalModelLieAlgebra :
    LieAlgebra ℂ A.ActualEquationKoszulLieModel :=
  MetabelianLieModel.modelLieAlgebra ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)

/-- The literal native quotient also carries the proved actual LCS
commutative group; the named piece is not substituted by a new object. -/
local instance comparisonLiteralLowerCentralCommGroup (G : Type*) [Group G] (n : ℕ) :
    CommGroup (lowerCentralSeries G n ⧸ nextLowerCentralIn G n) :=
  lowerCentralPiece_commGroup G n

/-- The generic finite model uses the same native raising quotient
family as the actual configuration specialization. -/
local instance comparisonGenericFinitePieceGroups (k V : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [_root_.Module k V]
    {j : Type*} [Fintype j] (b : _root_.Module.Basis j k V)
    (K : Submodule k (⋀[k]^2 V)) (t : ℕ) :
    (i : ℕ) → AddCommGroup (DegreeRaisingPiece k
      (NativeDerivationExtension k (finiteModelTruncation k V b K t)
        (nativeEulerDerivation k (finiteModelTruncation k V b K t)
          (finiteModelComponent k V b K t)))
      (nativeEulerExtensionFlag k (finiteModelTruncation k V b K t)
        (finiteModelComponent k V b K t)) i) :=
  comparisonRaisingPieceGroups k
    (NativeDerivationExtension k (finiteModelTruncation k V b K t)
      (nativeEulerDerivation k (finiteModelTruncation k V b K t)
        (finiteModelComponent k V b K t)))
    (nativeEulerExtensionFlag k (finiteModelTruncation k V b K t)
      (finiteModelComponent k V b K t))

/-- A generic first-piece identity, proved before specializing the
native quotient dictionaries to the actual complement. -/
private theorem comparisonFirstChenOriginalClass (k G : Type)
    [Field k] [CharZero k] [Group G] (g : G) :
    scalarFirstChenEquiv G k (GroupComparison.originalScalarFirstClass k G g) =
      (1 : k) ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn (metabelianQuotient G) 0)
          (lowerCentralRepresentativeMap
            (QuotientGroup.mk' (derivedSeries G 2) : G →* metabelianQuotient G) 0
            (⟨g, Subgroup.mem_top g⟩ : lowerCentralSeries G 0))) := by
  change scalarFirstChenEquiv G k ((1 : k) ⊗ₜ[ℤ]
    Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G 0)
      (⟨g, Subgroup.mem_top g⟩ : lowerCentralSeries G 0))) = _
  rw [scalarFirstChenEquiv_tmul, ← lowerCentralPieceMap_firstChen_eq]
  simp only [toMul_ofMul]
  rw [lowerCentralPieceMap_mk]
  rfl

/-- Actual tensor extension of classes is generated by the original
native group representatives. This universal-property step is generic. -/
private theorem comparisonScalarFirst_ext (k G : Type) (M : Type*)
    [Field k] [CharZero k] [Group G] [AddCommGroup M] [_root_.Module k M]
    (f g : scalarLowerCentralPiece k G 0 →ₗ[k] M)
    (h : ∀ x : G, f (GroupComparison.originalScalarFirstClass k G x) =
      g (GroupComparison.originalScalarFirstClass k G x)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a u =>
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (nextLowerCentralIn G 0)
      (Additive.toMul u)
    have hu : Additive.ofMul (QuotientGroup.mk' (nextLowerCentralIn G 0) v) = u :=
      congrArg Additive.ofMul hv
    rw [← hu]
    have ht : a ⊗ₜ[ℤ] Additive.ofMul
        (QuotientGroup.mk' (nextLowerCentralIn G 0) v) =
        a • GroupComparison.originalScalarFirstClass k G (v : G) := by
      change a ⊗ₜ[ℤ] Additive.ofMul
          (QuotientGroup.mk' (nextLowerCentralIn G 0) v) =
        a • ((1 : k) ⊗ₜ[ℤ] Additive.ofMul
          (QuotientGroup.mk' (nextLowerCentralIn G 0) v))
      rw [TensorProduct.smul_tmul']
      simp only [smul_eq_mul, mul_one]
    calc
      f (a ⊗ₜ[ℤ] Additive.ofMul
          (QuotientGroup.mk' (nextLowerCentralIn G 0) v)) =
          f (a • GroupComparison.originalScalarFirstClass k G (v : G)) :=
        congrArg f ht
      _ = a • f (GroupComparison.originalScalarFirstClass k G (v : G)) :=
        f.map_smul a _
      _ = a • g (GroupComparison.originalScalarFirstClass k G (v : G)) :=
        congrArg (fun z : M => a • z) (h (v : G))
      _ = g (a • GroupComparison.originalScalarFirstClass k G (v : G)) :=
        (g.map_smul a _).symm
      _ = g (a ⊗ₜ[ℤ] Additive.ofMul
          (QuotientGroup.mk' (nextLowerCentralIn G 0) v)) :=
        (congrArg g ht).symm

/-- The actual associated Lie algebra of the actual finite Euler flag. -/
abbrev ActualFiniteEulerLeadingLie :=
  flagAssociatedGraded ℂ (A.ActualFiniteLogarithmicEulerSpace c)
    (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c))

/-- The same original Chen Lie maps through the genuine finite
metabelian monodromy into the genuine associated operator Lie algebra. -/
def actualFiniteEulerChenLeadingLieHom (base : A.Complement) :
    scalarChenAssociatedGraded ℂ (FundamentalGroup A.Complement base) →ₗ⁅ℂ⁆
      A.ActualFiniteEulerLeadingLie c :=
  nativeEulerExponentialGroupLeadingLieHom ℂ
    (metabelianQuotient (FundamentalGroup A.Complement base))
    (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c)
    (A.actualFiniteLogarithmicComponent_zero c) c
    (A.actualFiniteLogarithmicComponent_above c)
    (A.actualFiniteEulerChenMonodromy c base)

variable (hc : 1 ≤ c)

/-- The actual original first group representatives obey the calculated
monodromy identity after the actual projection to the Chen group. -/
theorem actualFiniteEulerChenLeading_first_originalClass
    (base : A.Complement) (g : FundamentalGroup A.Complement base) :
    A.actualFiniteEulerChenLeadingLieHom c base
      (scalarGroupGradedInclusion ℂ
        (metabelianQuotient (FundamentalGroup A.Complement base)) 0
        (scalarFirstChenEquiv (FundamentalGroup A.Complement base) ℂ
          (GroupComparison.originalScalarFirstClass ℂ
            (FundamentalGroup A.Complement base) g))) =
      flagGradedInclusion ℂ (A.ActualFiniteLogarithmicEulerSpace c)
        (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)) 1
        (nativeEulerAbelianLeading ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)
          (A.actualFiniteLogarithmicComponent_zero c)
          ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm
            ((A.actualEquationDualScalarFirst ℂ base).symm
              (GroupComparison.originalScalarFirstClass ℂ
                (FundamentalGroup A.Complement base) g)))) := by
  let G := FundamentalGroup A.Complement base
  let p : G →* metabelianQuotient G := QuotientGroup.mk' (derivedSeries G 2)
  let g₀ : lowerCentralSeries G 0 := ⟨g, Subgroup.mem_top g⟩
  let g₁ := lowerCentralRepresentativeMap p 0 g₀
  have h := nativeEulerExponentialGroupLeading_first_representative ℂ
    (metabelianQuotient G) (A.ActualFiniteLogarithmicLie c)
    (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)
    c (A.actualFiniteLogarithmicComponent_above c)
    (A.actualFiniteEulerChenMonodromy c base) g₁
  change A.actualFiniteEulerChenLeadingLieHom c base
      (scalarGroupGradedInclusion ℂ (metabelianQuotient G) 0
        ((1 : ℂ) ⊗ₜ[ℤ] Additive.ofMul
          (QuotientGroup.mk' (nextLowerCentralIn (metabelianQuotient G) 0) g₁))) =
    flagGradedInclusion ℂ (A.ActualFiniteLogarithmicEulerSpace c)
      (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c)) 1
      (nativeEulerAbelianLeading ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)
        (Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
          (A.actualFiniteEulerMonodromy c base g)))) at h
  rw [A.actualFiniteEulerAxisCharacter_originalFirstClass c hc base g] at h
  have hs := comparisonFirstChenOriginalClass ℂ G g
  have hs' := congrArg
    (fun z : scalarLowerCentralPiece ℂ (metabelianQuotient G) 0 =>
      A.actualFiniteEulerChenLeadingLieHom c base
        (scalarGroupGradedInclusion ℂ (metabelianQuotient G) 0 z)) hs
  exact hs'.trans h

/-- The first representative identity extends to every actual scalar
first quotient class. Actual quotient representatives and the genuine
tensor universal property supply the extension. -/
theorem actualFiniteEulerChenLeading_first_inclusion
    (base : A.Complement)
    (x : scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0) :
    A.actualFiniteEulerChenLeadingLieHom c base
      (scalarGroupGradedInclusion ℂ
        (metabelianQuotient (FundamentalGroup A.Complement base)) 0
        (scalarFirstChenEquiv (FundamentalGroup A.Complement base) ℂ x)) =
      flagGradedInclusion ℂ (A.ActualFiniteLogarithmicEulerSpace c)
        (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)) 1
        (nativeEulerAbelianLeading ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)
          ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm
            ((A.actualEquationDualScalarFirst ℂ base).symm x))) := by
  let f : scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0 →ₗ[ℂ]
      A.ActualFiniteEulerLeadingLie c :=
    (A.actualFiniteEulerChenLeadingLieHom c base).toLinearMap.comp
      ((scalarGroupGradedInclusion ℂ
        (metabelianQuotient (FundamentalGroup A.Complement base)) 0).comp
        (scalarFirstChenEquiv (FundamentalGroup A.Complement base) ℂ).toLinearMap)
  let g : scalarLowerCentralPiece ℂ (FundamentalGroup A.Complement base) 0 →ₗ[ℂ]
      A.ActualFiniteEulerLeadingLie c :=
    (flagGradedInclusion ℂ (A.ActualFiniteLogarithmicEulerSpace c)
      (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c)) 1).comp
      ((nativeEulerAbelianLeading ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)).comp
        ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm.toLinearMap.comp
          (A.actualEquationDualScalarFirst ℂ base).symm.toLinearMap))
  have heq : f = g := comparisonScalarFirst_ext ℂ
    (FundamentalGroup A.Complement base) (A.ActualFiniteEulerLeadingLie c) f g
    (fun y => A.actualFiniteEulerChenLeading_first_originalClass c hc base y)
  exact LinearMap.congr_fun heq x

/-- The actual abelian coordinate inverse retains every original
vector generator, beyond just the original coordinate projections. -/
theorem actualFiniteEulerAxisOriginalEquiv_symm_originalGenerator
    (u : _root_.Module.Dual ℂ (ι → ℂ)) :
    (A.actualFiniteEulerAxisOriginalEquiv c hc).symm u =
      (nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
        (A.actualFiniteLogarithmicComponent c) 2).mkQ
        (finiteModelProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c
          (MetabelianLieModel.generatorInclusion ℂ (_root_.Module.Dual ℂ (ι → ℂ))
            (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)) := by
  apply (A.actualFiniteEulerAxisOriginalEquiv c hc).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (finiteModelAbelianOriginalEquiv_originalGenerator ℂ
    (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c hc u).symm

/-- The genuine finite generator comparison is first checked on the
generic original model, before the actual geometry is substituted. -/
private theorem comparisonFiniteGeneratorLeading (k V : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [_root_.Module k V]
    {j : Type*} [Fintype j] (b : _root_.Module.Basis j k V)
    (K : Submodule k (⋀[k]^2 V)) (t : ℕ) (v : V) :
    flagGradedInclusion k
        (NativeDerivationExtension k (finiteModelTruncation k V b K t)
          (nativeEulerDerivation k (finiteModelTruncation k V b K t)
            (finiteModelComponent k V b K t)))
        (nativeEulerExtensionFlag k (finiteModelTruncation k V b K t)
          (finiteModelComponent k V b K t)) 1
        (nativeEulerAbelianLeading k (finiteModelTruncation k V b K t)
          (finiteModelComponent k V b K t) (finiteModelComponent_zero k V b K t)
          ((nativeGradedTail k (finiteModelTruncation k V b K t)
            (finiteModelComponent k V b K t) 2).mkQ
            (finiteModelProjection k V b K t
              (MetabelianLieModel.generatorInclusion k V K v)))) =
      originalModelFiniteLeading k V b K t
        (MetabelianLieModel.generatorInclusion k V K v) := by
  rw [nativeEulerAbelianLeading_mk, originalModelFiniteLeading_generator]
  congr 1

include hc in
/-- Genuine original generator values determine the entire composition
through the actual original Chen Lie. No composition equality is assumed. -/
theorem actualEquationKoszulModelToChen_finiteLeading_composition (base : A.Complement) :
    (A.actualFiniteEulerChenLeadingLieHom c base).comp
      (A.actualEquationKoszulModelToChen base) =
      originalModelFiniteLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
        A.actualLogHolonomyLabelBasis.dualBasis
        (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c := by
  have hgen (u : _root_.Module.Dual ℂ (ι → ℂ)) :
      A.actualFiniteEulerChenLeadingLieHom c base
          (A.actualEquationKoszulModelToChen base
            (MetabelianLieModel.generatorInclusion ℂ
              (_root_.Module.Dual ℂ (ι → ℂ))
              (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)) =
        originalModelFiniteLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c
          (MetabelianLieModel.generatorInclusion ℂ
            (_root_.Module.Dual ℂ (ι → ℂ))
            (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u) := by
    let l : A.ActualFiniteEulerAxisQuotient c →ₗ[ℂ]
        A.ActualFiniteEulerLeadingLie c :=
      (flagGradedInclusion ℂ (A.ActualFiniteLogarithmicEulerSpace c)
        (nativeEulerExtensionFlag ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)) 1).comp
        (nativeEulerAbelianLeading ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c)
          (A.actualFiniteLogarithmicComponent_zero c))
    calc
      A.actualFiniteEulerChenLeadingLieHom c base
          (A.actualEquationKoszulModelToChen base
            (MetabelianLieModel.generatorInclusion ℂ
              (_root_.Module.Dual ℂ (ι → ℂ))
              (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u)) =
          A.actualFiniteEulerChenLeadingLieHom c base
            (scalarGroupGradedInclusion ℂ
              (metabelianQuotient (FundamentalGroup A.Complement base)) 0
              (scalarFirstChenEquiv (FundamentalGroup A.Complement base) ℂ
                (A.actualEquationDualScalarFirst ℂ base u))) :=
        congrArg (A.actualFiniteEulerChenLeadingLieHom c base)
          (A.actualEquationKoszulModelToChen_generator base u)
      _ = l ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm
          ((A.actualEquationDualScalarFirst ℂ base).symm
            (A.actualEquationDualScalarFirst ℂ base u))) :=
        A.actualFiniteEulerChenLeading_first_inclusion c hc base
          (A.actualEquationDualScalarFirst ℂ base u)
      _ = l ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm u) :=
        congrArg (fun z : _root_.Module.Dual ℂ (ι → ℂ) =>
          l ((A.actualFiniteEulerAxisOriginalEquiv c hc).symm z))
          ((A.actualEquationDualScalarFirst ℂ base).symm_apply_apply u)
      _ = l ((nativeGradedTail ℂ (A.ActualFiniteLogarithmicLie c)
          (A.actualFiniteLogarithmicComponent c) 2).mkQ
          (finiteModelProjection ℂ (_root_.Module.Dual ℂ (ι → ℂ))
            A.actualLogHolonomyLabelBasis.dualBasis
            (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c
            (MetabelianLieModel.generatorInclusion ℂ
              (_root_.Module.Dual ℂ (ι → ℂ))
              (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u))) :=
        congrArg l (A.actualFiniteEulerAxisOriginalEquiv_symm_originalGenerator c hc u)
      _ = originalModelFiniteLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c
          (MetabelianLieModel.generatorInclusion ℂ
            (_root_.Module.Dual ℂ (ι → ℂ))
            (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) u) :=
        comparisonFiniteGeneratorLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
          A.actualLogHolonomyLabelBasis.dualBasis
          (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c u
  exact originalKoszulLieHom_comp_eq_of_generators ℂ
    (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel)
    (A.actualEquationKoszulModelToChen base)
    (A.actualFiniteEulerChenLeadingLieHom c base)
    (originalModelFiniteLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c) hgen

/-- Genuine positive bounds alone suffice in the original homogeneous
model. The proof uses its native finite decomposition. -/
private theorem comparisonOriginalPositiveLeading (k V : Type*)
    [Field k] [CharZero k] [AddCommGroup V] [_root_.Module k V]
    {j : Type*} [Fintype j] (b : _root_.Module.Basis j k V)
    (K : Submodule k (⋀[k]^2 V)) (x : MetabelianLieModel k V K)
    (hx : ∀ c : ℕ, 1 ≤ c → originalModelFiniteLeading k V b K c x = 0) : x = 0 := by
  have hp (n : ℕ) : modelPositiveProjection k V b K n x = 0 := by
    have hproj := (originalModelFiniteLeading_eq_zero_iff k V b K (n + 1) x).mp
      (hx (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hproj
    exact LinearMap.mem_ker.mp (modelTruncationIdeal_le_projection_ker k V b K
      (n + 1) n (Nat.le_succ n) hmem)
  obtain ⟨N, hN⟩ := modelPositiveProjection_finite_sum k V b K x
  exact hN.trans (by simp only [hp, Finset.sum_const_zero, zero_add])

/-- The genuine positive-bound family separates the original model.
No dimension or separation property of the Chen target is used. -/
theorem actualEquationModel_eq_zero_of_positive_finiteLeading
    (x : A.ActualEquationKoszulLieModel)
    (hx : ∀ c : ℕ, 1 ≤ c → originalModelFiniteLeading ℂ
      (_root_.Module.Dual ℂ (ι → ℂ)) A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c x = 0) : x = 0 := by
  exact comparisonOriginalPositiveLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
    A.actualLogHolonomyLabelBasis.dualBasis
    (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) x hx

/-- The actual original paper Koszul model injects into the same
original based fundamental group's actual scalar Chen Lie. It follows
from the proved genuine finite leading compositions and their genuine
joint separation, with no injectivity or formality premise. -/
theorem actualEquationKoszulModelToChen_injective (base : A.Complement) :
    Function.Injective (A.actualEquationKoszulModelToChen base) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply A.actualEquationModel_eq_zero_of_positive_finiteLeading
  intro c hc
  have h := DFunLike.congr_fun
    (A.actualEquationKoszulModelToChen_finiteLeading_composition c hc base) (x - y)
  change A.actualFiniteEulerChenLeadingLieHom c base
      (A.actualEquationKoszulModelToChen base (x - y)) =
    originalModelFiniteLeading ℂ (_root_.Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c (x - y) at h
  rw [map_sub, hxy, sub_self, map_zero] at h
  exact h.symm

end ChenRanks.AffineArrangement
