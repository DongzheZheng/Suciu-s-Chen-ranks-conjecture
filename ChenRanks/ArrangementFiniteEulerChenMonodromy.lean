import ChenRanks.ArrangementFiniteEulerPrincipalCovering
import ChenRanks.KoszulFiniteModelTailAbelian
import ChenRanks.NativeEulerExponentCommutativity
import ChenRanks.NativeLieAutomorphismUnits
import ChenRanks.ChenObjects

/-! The actual original finite monodromy factors through the actual
maximal metabelian quotient. Its target's second derived subgroup vanishes
because the original finite Koszul model's actual degree-two tail is
abelian. This is a conclusion of the original structures, not a chosen
metabelian group law or a representation assumption.
-/
noncomputable section
namespace ChenRanks.AffineArrangement
open LieComparison
variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι) (c : ℕ)

/-- The original second derived subgroup of the actual finite group vanishes. -/
theorem actualFiniteEulerExponentialGroup_secondDerived_eq_bot :
    derivedSeries (A.ActualFiniteEulerExponentialGroup c) 2 = ⊥ :=
  nativeEulerExponentialGroup_secondDerived_eq_bot ℂ
    (A.ActualFiniteLogarithmicLie c) (A.actualFiniteLogarithmicComponent c)
    (A.actualFiniteLogarithmicComponent_zero c) c
    (A.actualFiniteLogarithmicComponent_above c)
    (Koszul.finiteModelTail_two_isAbelian ℂ (Module.Dual ℂ (ι → ℂ))
      A.actualLogHolonomyLabelBasis.dualBasis
      (Koszul.exteriorAnnihilator ℂ (ι → ℂ) 2 A.rationalQuadraticKernel) c)

/-- The actual original second derived subgroup is killed by the actual
representation, using the native functoriality of the genuine derived series. -/
theorem actualFiniteEulerMonodromy_secondDerived_le_kernel (base : A.Complement) :
    derivedSeries (FundamentalGroup A.Complement base) 2 ≤
      (A.actualFiniteEulerMonodromy c base).ker := by
  apply (Subgroup.map_eq_bot_iff _).mp
  apply le_bot_iff.mp
  exact (map_derivedSeries_le_derivedSeries
    (A.actualFiniteEulerMonodromy c base) 2).trans
    (A.actualFiniteEulerExponentialGroup_secondDerived_eq_bot c).le

/-- A representation of the actual original maximal metabelian quotient,
constructed by the native quotient universal property. -/
def actualFiniteEulerChenMonodromy (base : A.Complement) :
    metabelianQuotient (FundamentalGroup A.Complement base) →*
      A.ActualFiniteEulerExponentialGroup c :=
  QuotientGroup.lift (derivedSeries (FundamentalGroup A.Complement base) 2)
    (A.actualFiniteEulerMonodromy c base)
    (A.actualFiniteEulerMonodromy_secondDerived_le_kernel c base)

@[simp] theorem actualFiniteEulerChenMonodromy_mk
    (base : A.Complement) (g : FundamentalGroup A.Complement base) :
    A.actualFiniteEulerChenMonodromy c base
      (QuotientGroup.mk' (derivedSeries (FundamentalGroup A.Complement base) 2) g) =
      A.actualFiniteEulerMonodromy c base g := rfl

/-- The same actual monodromy acts by genuine units of the same original
Euler extension's endomorphism ring, with its actual multiplication. -/
def actualFiniteEulerChenMonodromyUnits (base : A.Complement) :
    metabelianQuotient (FundamentalGroup A.Complement base) →*
      (Module.End ℂ (A.ActualFiniteLogarithmicEulerSpace c))ˣ :=
  (nativeLieAutomorphismUnitsEnd ℂ (A.ActualFiniteLogarithmicEulerSpace c)).comp
    ((nativeEulerExponentialSubgroup ℂ (A.ActualFiniteLogarithmicLie c)
      (A.actualFiniteLogarithmicComponent c) (A.actualFiniteLogarithmicComponent_zero c)
      c (A.actualFiniteLogarithmicComponent_above c)).subtype.comp
        (A.actualFiniteEulerChenMonodromy c base))

@[simp] theorem actualFiniteEulerChenMonodromyUnits_apply
    (base : A.Complement)
    (g : metabelianQuotient (FundamentalGroup A.Complement base))
    (p : A.ActualFiniteLogarithmicEulerSpace c) :
    (A.actualFiniteEulerChenMonodromyUnits c base g :
      Module.End ℂ (A.ActualFiniteLogarithmicEulerSpace c)) p =
      (A.actualFiniteEulerChenMonodromy c base g).val p := rfl

end ChenRanks.AffineArrangement
