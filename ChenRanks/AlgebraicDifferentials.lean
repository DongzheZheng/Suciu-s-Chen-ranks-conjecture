import Mathlib

/-!
# Relative differentials of algebraic elements

This module concerns actual derivations and actual Kähler differentials of
field extensions.  In characteristic zero, an element algebraic over the
base field has zero relative differential.  The proof differentiates its
separable minimal polynomial; differential vanishing is not an assumption.

This is only the final field-theoretic step of a possible replacement for
the manuscript's proper-fibre argument.  No statement here asserts that
vanishing horizontal valuations implies algebraicity, constructs residues,
or proves arrangement separation or the Chen ranks formula.
-/

namespace ChenRanks

variable {L F M : Type*} [Field L] [CharZero L] [Field F] [Algebra L F]
  [AddCommGroup M] [Module F M] [Module L M]

/-- An actual base-linear derivation kills every element algebraic over the
characteristic-zero base field. -/
theorem derivation_eq_zero_of_isAlgebraic
    (D : Derivation L F M) (a : F) (ha : IsAlgebraic L a) : D a = 0 := by
  have hsep : (minpoly L a).Separable :=
    (minpoly.irreducible ha.isIntegral).separable
  have hc : Polynomial.aeval a (Polynomial.derivative (minpoly L a)) ≠ 0 :=
    hsep.aeval_derivative_ne_zero (minpoly.aeval L a)
  have hz : Polynomial.aeval a (Polynomial.derivative (minpoly L a)) • D a = 0 := by
    simpa only [minpoly.aeval, map_zero] using (D.map_aeval (minpoly L a) a).symm
  calc
    D a = (Polynomial.aeval a (Polynomial.derivative (minpoly L a)))⁻¹ •
        (Polynomial.aeval a (Polynomial.derivative (minpoly L a)) • D a) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = 0 := by rw [hz, smul_zero]

/-- The actual universal relative differential of an algebraic element
vanishes; no relative-differential vanishing hypothesis is introduced. -/
theorem relative_differential_eq_zero_of_isAlgebraic
    (a : F) (ha : IsAlgebraic L a) : KaehlerDifferential.D L F a = 0 := by
  exact derivation_eq_zero_of_isAlgebraic (KaehlerDifferential.D L F) a ha

/-- The actual relative logarithmic differential of an algebraic element
vanishes.  Nonzeroness is needed for its logarithmic interpretation, not
for the displayed scalar-multiplication equality. -/
theorem relative_logarithmic_differential_eq_zero_of_isAlgebraic
    (a : F) (ha : IsAlgebraic L a) :
    a⁻¹ • KaehlerDifferential.D L F a = 0 := by
  rw [relative_differential_eq_zero_of_isAlgebraic a ha, smul_zero]

section Absolute

variable (C : Type*) [Field C] [Algebra C L] [Algebra C F] [IsScalarTower C L F]

/-- An actual absolute differential of an `L`-algebraic element lies in the
image of base-field differentials.  The image conclusion follows from the
actual Kähler transitivity exact sequence, rather than being assumed. -/
theorem algebraic_differential_mem_baseChange_range
    (a : F) (ha : IsAlgebraic L a) :
    KaehlerDifferential.D C F a ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange C L F) := by
  apply (KaehlerDifferential.exact_mapBaseChange_map C L F _).mp
  simpa using relative_differential_eq_zero_of_isAlgebraic a ha

/-- The actual logarithmic differential of an `L`-algebraic element is a
linear combination over `F` of the absolute differentials from `L`. -/
theorem algebraic_logarithmic_differential_mem_baseChange_range
    (a : F) (ha : IsAlgebraic L a) :
    a⁻¹ • KaehlerDifferential.D C F a ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange C L F) := by
  exact (LinearMap.range (KaehlerDifferential.mapBaseChange C L F)).smul_mem
    a⁻¹ (algebraic_differential_mem_baseChange_range C a ha)

end Absolute

end ChenRanks
