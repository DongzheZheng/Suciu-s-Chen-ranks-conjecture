import ChenRanks.KoszulCanonicalFamilyGradingFunctionObjects

/-! Completely defined original zero and addition equations. Each body
is the same literal equality for the same underlying native function;
none of these definitions contains equality evidence. -/

noncomputable section

open scoped DirectSum

namespace ChenRanks.Koszul

open ChenRanks.Resonance

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (I : Submodule k (⋀[k]^2 E))

/- Reuse the very same original target operation parents stored in the
unchanged function objects; no second operation dictionary is built. -/
attribute [local instance 4000] gradingFunctionTargetZero gradingFunctionTargetAdd

attribute [local instance 2500]
  registeredNativeOriginalGroup registeredNativeOriginalMonoid
  registeredNativeOriginalBaseCoefficients
attribute [local instance 2000]
  registeredFamilyComponentGroups registeredFamilyComponentMonoids
  registeredFamilyComponentBaseCoefficients registeredFamilyTargetGroup
  registeredFamilyTargetMonoid registeredFamilyTargetBaseCoefficients
  registeredHomogeneousGroups registeredHomogeneousMonoids registeredHomogeneousCoefficients
  registeredFamilyDegreeGroups registeredFamilyDegreeMonoids registeredFamilyDegreeCoefficients
attribute [local instance 3500]
  sharedDegreeParents sharedDegreeCoefficients sharedOriginalParents sharedOriginalCoefficients

variable {ι : Type*} [Fintype ι]
variable (b : _root_.Module.Basis ι k (_root_.Module.Dual k E))
variable [CharZero k]
variable (hsep : ∀ P : Submodule k E,
  IsMaximalIsotropic (relationWedge (cupQuotient I)) P →
  2 ≤ _root_.Module.finrank k P → mixedExterior P ⊓ I = pureExterior P)

/-- The complete original left zero equation. -/
def canonicalFamilyGradingLeftZeroEquation : Prop :=
  canonicalFamilyGradingLeftFunction k E I b hsep 0 = 0

omit [CharZero k] in
/-- The complete original right zero equation. -/
def canonicalFamilyGradingRightZeroEquation : Prop :=
  canonicalFamilyGradingRightFunction k E I b 0 = 0

/-- The complete original left addition equation. -/
def canonicalFamilyGradingLeftAddEquation
    (x y : ⨁ r, homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) : Prop :=
  canonicalFamilyGradingLeftFunction k E I b hsep (x + y) =
    canonicalFamilyGradingLeftFunction k E I b hsep x +
      canonicalFamilyGradingLeftFunction k E I b hsep y

omit [CharZero k] in
/-- The complete original right addition equation. -/
def canonicalFamilyGradingRightAddEquation
    (x y : ⨁ r, homogeneousModule k (_root_.Module.Dual k E) b
      (exteriorAnnihilator k E 2 I) r) : Prop :=
  canonicalFamilyGradingRightFunction k E I b (x + y) =
    canonicalFamilyGradingRightFunction k E I b x +
      canonicalFamilyGradingRightFunction k E I b y

end ChenRanks.Koszul
