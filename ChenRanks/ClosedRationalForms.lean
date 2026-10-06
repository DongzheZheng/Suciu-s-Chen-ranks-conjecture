import Mathlib
import ChenRanks.LogarithmicDifferentials
import ChenRanks.ExteriorSeparation

/-!
# Closed rational forms and the genuine Cartan identity

Closedness is expressed by the Cartan formula on all actual base-linear
derivations of the function field.  Evaluation uses the universal property
of the actual Kähler differential module, and the bracket is the actual
commutator of derivations.  This definition is independent of a curve field,
isotropy, or a desired separation conclusion.

Exact differentials and actual logarithmic differentials satisfy the formula.
Closedness is stable under constant-field linear combinations.  Comparing
the Cartan formulas for `ω` and `h • ω` gives the actual product differential
constraint.  The universal property and separating algebraic dual then turn
that constraint into a scalar multiple of `dh` whenever `dh` is nonzero,
and into a genuine zero exterior product without the nonzero hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

variable (C F : Type*) [Field C] [Field F] [Algebra C F]

/-- The Cartan closedness test on the actual rational differential module. -/
def IsClosedRationalForm (ω : Ω[F⁄C]) : Prop :=
  ∀ δ ε : Derivation C F F,
    δ (ε.liftKaehlerDifferential ω) - ε (δ.liftKaehlerDifferential ω) =
      ⁅δ, ε⁆.liftKaehlerDifferential ω

/-- An exact differential satisfies the Cartan formula by the definition
of the genuine commutator of derivations. -/
theorem differential_isClosed (h : F) :
    IsClosedRationalForm C F (KaehlerDifferential.D C F h) := by
  intro δ ε
  simp only [Derivation.liftKaehlerDifferential_comp_D, Derivation.commutator_apply]

theorem zero_isClosed : IsClosedRationalForm C F 0 := by
  intro δ ε
  simp

theorem add_isClosed {ω η : Ω[F⁄C]}
    (hω : IsClosedRationalForm C F ω) (hη : IsClosedRationalForm C F η) :
    IsClosedRationalForm C F (ω + η) := by
  intro δ ε
  have hω' := hω δ ε
  have hη' := hη δ ε
  simp only [map_add]
  linear_combination hω' + hη'

/-- Constants act linearly on closed forms; arbitrary function-field
coefficients need not preserve closedness. -/
theorem constant_smul_isClosed (c : C) {ω : Ω[F⁄C]}
    (hω : IsClosedRationalForm C F ω) :
    IsClosedRationalForm C F (c • ω) := by
  intro δ ε
  simp only [LinearMap.map_smul_of_tower]
  change δ.toLinearMap (c • ε.liftKaehlerDifferential ω) -
    ε.toLinearMap (c • δ.liftKaehlerDifferential ω) =
      c • ⁅δ, ε⁆.liftKaehlerDifferential ω
  rw [δ.toLinearMap.map_smul, ε.toLinearMap.map_smul]
  rw [← smul_sub]
  exact congrArg (fun x : F ↦ c • x) (hω δ ε)

/-- Actual closed forms constitute a subspace over the constant field. -/
def closedRationalForms : Submodule C Ω[F⁄C] where
  carrier := IsClosedRationalForm C F
  zero_mem' := zero_isClosed C F
  add_mem' := fun hω hη ↦ add_isClosed C F hω hη
  smul_mem' := fun c _ hω ↦ constant_smul_isClosed C F c hω

/-- The differential of the reciprocal cancels the symmetric cross terms
in the Cartan formula for an actual `dlog`. -/
theorem logarithmicDifferential_isClosed (u : Fˣ) :
    IsClosedRationalForm C F (logarithmicDifferential C F u) := by
  intro δ ε
  simp only [logarithmicDifferential, map_smul,
    Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul,
    Derivation.leibniz, Derivation.leibniz_inv, Derivation.commutator_apply]
  ring

/-- Every constant-field linear combination of genuine logarithmic
differentials is closed; logarithmic generation is not replaced by a
closedness hypothesis. -/
theorem logarithmicCombination_isClosed {ι : Type*} [Fintype ι]
    (u : ι → Fˣ) (β : ι → C) :
    IsClosedRationalForm C F (∑ i, β i • logarithmicDifferential C F (u i)) := by
  exact (closedRationalForms C F).sum_mem fun i _ ↦
    (closedRationalForms C F).smul_mem (β i) (logarithmicDifferential_isClosed C F (u i))

/-- Comparing the two actual Cartan identities yields the product rule
constraint `dh ∧ ω = 0` evaluated on arbitrary derivations. -/
theorem closed_smul_derivation_constraint (h : F) (ω : Ω[F⁄C])
    (hω : IsClosedRationalForm C F ω)
    (hhω : IsClosedRationalForm C F (h • ω)) (δ ε : Derivation C F F) :
    δ h * ε.liftKaehlerDifferential ω = ε h * δ.liftKaehlerDifferential ω := by
  have h₀ := hω δ ε
  have h₁ := hhω δ ε
  simp only [map_smul, smul_eq_mul, Derivation.leibniz] at h₁
  linear_combination h₁ - h * h₀

/-- A true differential dual gives an actual derivation by the universal
property, and evaluation recovers the original dual. -/
@[simp]
theorem differentialDual_derivation_lift (φ : Module.Dual F Ω[F⁄C]) :
    (KaehlerDifferential.linearMapEquivDerivation C F φ).liftKaehlerDifferential = φ :=
  (KaehlerDifferential.linearMapEquivDerivation C F).symm_apply_apply φ

@[simp]
theorem differentialDual_derivation_apply (φ : Module.Dual F Ω[F⁄C]) (h : F) :
    KaehlerDifferential.linearMapEquivDerivation C F φ h =
      φ (KaehlerDifferential.D C F h) := by
  rw [← Derivation.liftKaehlerDifferential_comp_D
    (KaehlerDifferential.linearMapEquivDerivation C F φ) h,
    differentialDual_derivation_lift]

/-- A nonzero `dh` and the genuine product differential constraint force
the actual rational form to be a scalar multiple of `dh`.  No finiteness
or assumed nondegeneracy of a pairing is needed for the algebraic dual. -/
theorem closed_form_eq_smul_differential (h : F) (ω : Ω[F⁄C])
    (hω : IsClosedRationalForm C F ω)
    (hhω : IsClosedRationalForm C F (h • ω))
    (hdh : KaehlerDifferential.D C F h ≠ 0) :
    ∃ a : F, a • KaehlerDifferential.D C F h = ω := by
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one F hdh
  refine ⟨φ₀ ω, ?_⟩
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff F _).mp
  intro φ
  simp only [map_sub, map_smul, smul_eq_mul]
  have ht := closed_smul_derivation_constraint C F h ω hω hhω
    (KaehlerDifferential.linearMapEquivDerivation C F φ₀)
    (KaehlerDifferential.linearMapEquivDerivation C F φ)
  simp only [differentialDual_derivation_lift, differentialDual_derivation_apply,
    hφ₀, one_mul] at ht
  rw [ht]
  ring

/-- Closedness of `ω` and of `hω` implies the actual exterior-product
identity, including the degenerate case `dh = 0`. -/
theorem closed_form_wedge_differential_eq_zero (h : F) (ω : Ω[F⁄C])
    (hω : IsClosedRationalForm C F ω)
    (hhω : IsClosedRationalForm C F (h • ω)) :
    exteriorWedge (k := F) (KaehlerDifferential.D C F h) ω = 0 := by
  by_cases hdh : KaehlerDifferential.D C F h = 0
  · apply Subtype.ext
    simp [exteriorWedge_coe, hdh]
  · obtain ⟨a, ha⟩ := closed_form_eq_smul_differential C F h ω hω hhω hdh
    rw [← ha]
    apply Subtype.ext
    simp [exteriorWedge_coe]

/-- In the curve construction, closedness of `a dh` forces the actual
identity `da ∧ dh = 0`; this identity is proved, not passed as an input. -/
theorem closed_smul_differential_wedge_eq_zero (a h : F)
    (hclosed : IsClosedRationalForm C F (a • KaehlerDifferential.D C F h)) :
    exteriorWedge (k := F) (KaehlerDifferential.D C F a)
      (KaehlerDifferential.D C F h) = 0 :=
  closed_form_wedge_differential_eq_zero C F a (KaehlerDifferential.D C F h)
    (differential_isClosed C F h) hclosed

end ChenRanks
