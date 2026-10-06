import ChenRanks.ArrangementFiniteEulerMeridianMonodromyCharacter
import ChenRanks.DiscretePrincipalFramePathTransport
import ChenRanks.ArrangementCharactersMeridianIdentification
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Actual finite monodromy characters in the original equation coordinates

The genuine covering character has the calculated positive logarithmic
period on every original meridian. Genuine covering transport identifies
this value at every original basepoint. The proved original meridian
cohomology basis then identifies every scalar character with its original
equation coefficients. No period, first-degree identification, presentation
or formality assumption is an input. The statement includes c=0, where
the original finite axis quotient and all its generator classes vanish.
-/

noncomputable section
namespace ChenRanks.AffineArrangement
open LieComparison TopologicalComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

local instance equationCharacterComplementPathConnected : PathConnectedSpace A.Complement :=
  A.complement_pathConnectedSpace_from_actual_equations
local instance equationCharacterQuotientNormedAddCommGroup :
    NormedAddCommGroup (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedAddCommGroup ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance equationCharacterQuotientNormedSpace :
    NormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c) :=
  nativeFiniteNormedSpace ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance equationCharacterQuotientRealNormedSpace :
    NormedSpace ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  NormedSpace.restrictScalars ℝ ℂ (A.ActualFiniteEulerAxisQuotient c)
local instance (priority := 4500) equationCharacterQuotientRealModule :
    Module ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (equationCharacterQuotientRealNormedSpace A c).toModule
local instance (priority := 4500) equationCharacterQuotientRealSMul :
    SMul ℝ (A.ActualFiniteEulerAxisQuotient c) :=
  (equationCharacterQuotientRealModule A c).toSMul
local instance equationCharacterGroupTopology :
    TopologicalSpace (A.ActualFiniteEulerExponentialGroup c) := ⊥
local instance equationCharacterGroupDiscrete :
    DiscreteTopology (A.ActualFiniteEulerExponentialGroup c) := ⟨rfl⟩

/-- A genuine scalar character of the genuine finite exponential group. -/
def actualFiniteEulerScalarAxisCharacter
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) :
    A.ActualFiniteEulerExponentialGroup c →* Multiplicative ℂ where
  toFun T := Multiplicative.ofAdd
    (ell (Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c T)))
  map_one' := by
    rw [(A.actualFiniteEulerAxisCharacter c).map_one]
    change Multiplicative.ofAdd (ell 0) = 1
    rw [map_zero]
    rfl
  map_mul' T S := by
    rw [(A.actualFiniteEulerAxisCharacter c).map_mul, toAdd_mul, map_add]
    exact ofAdd_add _ _

/-- The actual original fundamental-group character obtained from actual
monodromy and the same original axis character. -/
def actualFiniteEulerAxisMonodromyCharacter (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) :
    Additive (FundamentalGroup A.Complement base) →+ ℂ :=
  MonoidHom.toAdditiveLeft
    ((A.actualFiniteEulerScalarAxisCharacter c ell).comp
      (A.actualFiniteEulerMonodromy c base))

@[simp] theorem actualFiniteEulerAxisMonodromyCharacter_apply
    (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c))
    (g : FundamentalGroup A.Complement base) :
    A.actualFiniteEulerAxisMonodromyCharacter c base ell (Additive.ofMul g) =
      ell (Multiplicative.toAdd (A.actualFiniteEulerAxisCharacter c
        (A.actualFiniteEulerMonodromy c base g))) := rfl

/-- Genuine original basepoint transport and the calculated genuine
meridian period give the same actual coefficient at every basepoint. -/
theorem actualFiniteEulerAxisMonodromyCharacter_meridian
    (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) (H : ι) :
    ChenRanks.basedPathCharacterValue A.Complement ℂ base
      (A.actualFiniteEulerAxisMonodromyCharacter c base ell)
      (A.actualCharacterMeridianLoop H) =
      ell (A.actualFiniteEulerAxisGeneratorClass c H) := by
  have ht := discretePrincipalFrameMonodromy_character_basedLoop
    (A.actualFiniteEulerPrincipalFrameCover c)
    (A.actualFiniteEulerAxisCharacter c) base
    (A.meridianDiskPathMap H (A.actualMeridianDisk H) 0)
    (A.actualCharacterMeridianLoop H)
  change A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerMonodromy c base
        (ChenRanks.basedFundamentalPath A.Complement base
          (A.actualCharacterMeridianLoop H))) =
    A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerMonodromy c
        (A.meridianDiskPathMap H (A.actualMeridianDisk H) 0)
        (A.actualFiniteEulerMeridianFundamentalElement H (A.actualMeridianDisk H))) at ht
  change ell (Multiplicative.toAdd
    (A.actualFiniteEulerAxisCharacter c
      (A.actualFiniteEulerMonodromy c base
        (ChenRanks.basedFundamentalPath A.Complement base
          (A.actualCharacterMeridianLoop H))))) = _
  rw [ht, A.actualFiniteEulerAxisCharacter_meridian c H (A.actualMeridianDisk H)]

/-- The actual original coefficient character identity, with all meridian
and basepoint identities proved from the original objects. -/
theorem actualFiniteEulerMonodromy_equationCharacters
    (base : A.Complement)
    (ell : Module.Dual ℂ (A.ActualFiniteEulerAxisQuotient c)) :
    A.actualEquationCoefficientCharacters ℂ base
        (fun H => ell (A.actualFiniteEulerAxisGeneratorClass c H)) =
      A.actualFiniteEulerAxisMonodromyCharacter c base ell :=
  A.actualEquationCharacter_eq_of_actual_meridian_values ℂ base
    (fun H => ell (A.actualFiniteEulerAxisGeneratorClass c H))
    (A.actualFiniteEulerAxisMonodromyCharacter c base ell)
    (A.actualFiniteEulerAxisMonodromyCharacter_meridian c base ell)

end ChenRanks.AffineArrangement
