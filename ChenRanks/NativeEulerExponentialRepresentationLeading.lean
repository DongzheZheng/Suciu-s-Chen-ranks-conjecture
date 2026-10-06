import ChenRanks.NativeEulerAxisFirstLeading
import ChenRanks.ScalarGroupFlagLeadingLie

/-!
# Actual exponential-valued monodromy automatically gives the actual leading Lie map

A genuine original group homomorphism to the already constructed native
Euler exponential subgroup has a genuine unit-endomorphism representation.
Every deviation condition is derived from the actual subgroup theorem.
The original lower-central quotients therefore give a genuine leading
Lie map. Its first representative value is computed from the actual
axis character, with no supplied raising or first-term condition.

This is a generic structural application to an actual group homomorphism.
The actual configuration monodromy must still be constructed, and its
axis character periods must still be calculated on its genuine loops.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.LieComparison

variable (k G L : Type*) [Field k] [CharZero k] [Group G]
variable [LieRing L] [LieAlgebra k L]
variable (ℒ : ℕ → Submodule k L) [GradedLieAlgebra ℒ]
variable (hzero : ℒ 0 = ⊥) (c : ℕ) (hbound : ∀ i : ℕ, c < i → ℒ i = ⊥)
variable (χ : G →* nativeEulerExponentialSubgroup k L ℒ hzero c hbound)

/-- The original unit representation is the actual subgroup inclusion
followed by the genuine native unit-endomorphism representation. -/
def nativeEulerExponentialGroupUnits :
    G →* (Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)))ˣ :=
  (nativeLieAutomorphismUnitsEnd k
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))).comp
      ((nativeEulerExponentialSubgroup k L ℒ hzero c hbound).subtype.comp χ)

@[simp] theorem nativeEulerExponentialGroupUnits_apply (g : G) :
    nativeEulerExponentialGroupUnits k G L ℒ hzero c hbound χ g =
      nativeLieAutomorphismUnitsEnd k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ)) (χ g).val := rfl

/-- Every actual representation deviation raises by one, proved from
the actual native subgroup rather than an input representation condition. -/
theorem nativeEulerExponentialGroupUnits_raising (g : G) :
    (nativeEulerExponentialGroupUnits k G L ℒ hzero c hbound χ g :
      Module.End k (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))) - 1 ∈
      degreeRaisingEndomorphisms k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 1 :=
  nativeEulerExponentialSubgroup_raising_deviation k L ℒ hzero c hbound (χ g)

/-- The genuine degree-preserving leading Lie map from the original
group's actual lower-central quotients. No raising hypothesis is supplied. -/
def nativeEulerExponentialGroupLeadingLieHom :
    scalarGroupAssociatedGraded k G →ₗ⁅k⁆ flagAssociatedGraded k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) :=
  scalarGroupFlagLeadingLieHom k G
    (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
    (nativeEulerExtensionFlag k L ℒ) (nativeEulerExtensionFlag_antitone k L ℒ)
    (nativeEulerExponentialGroupUnits k G L ℒ hzero c hbound χ)
    (nativeEulerExponentialGroupUnits_raising k G L ℒ hzero c hbound χ)

/-- On the genuine original ordinary degree-one representatives, the
actual leading Lie map equals the actual original axis character map. -/
theorem nativeEulerExponentialGroupLeading_first_representative
    (g : lowerCentralSeries G 0) :
    nativeEulerExponentialGroupLeadingLieHom k G L ℒ hzero c hbound χ
      (scalarGroupGradedInclusion k G 0
        ((1 : k) ⊗ₜ[ℤ]
          Additive.ofMul (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G 0) g))) =
      flagGradedInclusion k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 1
        (nativeEulerAbelianLeading k L ℒ hzero
          (Multiplicative.toAdd
            (nativeEulerAxisAbelianCharacter k L ℒ hzero c hbound (χ (g : G))))) := by
  change scalarGroupFlagLeadingLieHom k G
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) (nativeEulerExtensionFlag_antitone k L ℒ)
      (nativeEulerExponentialGroupUnits k G L ℒ hzero c hbound χ)
      (nativeEulerExponentialGroupUnits_raising k G L ℒ hzero c hbound χ)
      (scalarGroupGradedInclusion k G 0
        ((1 : k) ⊗ₜ[ℤ]
          Additive.ofMul (QuotientGroup.mk' (ChenRanks.nextLowerCentralIn G 0) g))) = _
  rw [scalarGroupFlagLeadingLieHom_inclusion, scalarLowerCentralFlagLeadingMap_tmul,
    one_smul, lowerCentralPieceFlagLeadingCharacter_mk]
  change flagGradedInclusion k
      (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
      (nativeEulerExtensionFlag k L ℒ) 1
      ((nextDegreeRaisingWithin k
        (NativeDerivationExtension k L (nativeEulerDerivation k L ℒ))
        (nativeEulerExtensionFlag k L ℒ) 1).mkQ
        (nativeEulerExponentialDifferenceCurrent k L ℒ hzero c hbound (χ (g : G)))) = _
  rw [nativeEulerExponentialFirstLeading_eq_axisCharacter]

end ChenRanks.LieComparison
