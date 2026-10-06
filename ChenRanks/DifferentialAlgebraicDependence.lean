import Mathlib
import ChenRanks.AlgebraicDifferentials
import ChenRanks.ExteriorSeparation

/-!
# Actual Kähler differentials and algebraic dependence

The ambient field is essentially of finite type over a characteristic-zero
base field, as is the function field of a complex variety.  Nonvanishing of
the universal differential is proved using the actual rational-function
field, localization of polynomial differentials, and the Jacobi–Zariski
sequence.  No differential-independence detector is an input assumption.

The exterior-square implication is obtained from an actual linear
contraction on the exterior square.  Mapping to the relative differential
module over the actual field `C(h)` then proves algebraicity.
-/

noncomputable section

open Polynomial TensorProduct
open scoped TensorProduct

namespace ChenRanks

section RationalFunction

variable (C : Type*) [Field C]

/-- The universal differential of the actual rational-function variable is
nonzero.  This follows from polynomial differentials and localization. -/
theorem rationalFunction_variable_differential_ne_zero :
    KaehlerDifferential.D C (RatFunc C) RatFunc.X ≠ 0 := by
  letI : Algebra.FormallyEtale C[X] (RatFunc C) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors C[X])
  let ψ : Ω[C[X]⁄C] →ₗ[C[X]] RatFunc C :=
    (LinearMap.toSpanSingleton C[X] (RatFunc C) 1).comp
      (KaehlerDifferential.polynomialEquiv C).toLinearMap
  have hψ : ψ (KaehlerDifferential.D C C[X] Polynomial.X) = 1 := by
    simp [ψ, KaehlerDifferential.polynomialEquiv_D]
  intro hz
  have ht : (1 : RatFunc C) ⊗ₜ[C[X]]
      KaehlerDifferential.D C C[X] Polynomial.X = 0 := by
    have h := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
      C C[X] (RatFunc C) Polynomial.X
    rw [RatFunc.algebraMap_X, hz, map_zero] at h
    exact h.symm
  have h := congrArg (ψ.liftBaseChange (RatFunc C)) ht
  have hone : (1 : RatFunc C) = 0 := by
    simp only [LinearMap.liftBaseChange_tmul, hψ, one_smul, map_zero] at h
    exact h
  exact one_ne_zero hone

end RationalFunction

section BaseChange

variable (C K F : Type*) [Field C] [Field K] [Field F]
  [Algebra C K] [Algebra C F] [Algebra K F] [IsScalarTower C K F]

/-- Actual differential base change is injective for a formally smooth
extension.  The proof uses the already-proved Jacobi–Zariski sequence. -/
theorem differential_baseChange_injective [Algebra.FormallySmooth K F] :
    Function.Injective (KaehlerDifferential.mapBaseChange C K F) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange C K F x).mp hx
  rw [Subsingleton.elim z 0, map_zero]

/-- A differential with coefficient in the source field is the image of
that actual coefficient differential under the field inclusion. -/
theorem differential_coefficient_mem_map_range (s h : K) :
    algebraMap K F s • KaehlerDifferential.D C F (algebraMap K F h) ∈
      LinearMap.range (KaehlerDifferential.map C C K F) := by
  refine ⟨s • KaehlerDifferential.D C K h, ?_⟩
  rw [map_smul, KaehlerDifferential.map_D]
  exact (algebraMap_smul F s _).symm

end BaseChange

section AlgebraicallyClosedBase

variable (C : Type*) [Field C] [IsAlgClosed C]
variable {F : Type*} [Field F] [Algebra C F]

/-- Over an algebraically closed base field, an element outside the actual
image of the base field is transcendental. -/
theorem transcendental_of_not_mem_base (h : F)
    (hn : h ∉ Set.range (algebraMap C F)) : Transcendental C h := by
  intro ha
  let L := IntermediateField.adjoin C {h}
  letI : Algebra.IsAlgebraic C L :=
    IntermediateField.isAlgebraic_adjoin_simple ha.isIntegral
  have hbot : L = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic L
  have hmem : h ∈ L := IntermediateField.subset_adjoin C {h} (by simp)
  rw [hbot] at hmem
  exact hn (IntermediateField.mem_bot.mp hmem)

end AlgebraicallyClosedBase

section FiniteTypeField

variable (C : Type*) [Field C] [CharZero C]
variable {F : Type*} [Field F] [Algebra C F] [Algebra.EssFiniteType C F]

/-- The actual embedding `C(X) → F` attached to a transcendental `h`, with
image the intermediate field `C(h)`. -/
def dependenceRatFuncMap (h : F) (hh : Transcendental C h) : RatFunc C →ₐ[C] F :=
  (IntermediateField.adjoin C {h}).val.comp
    (RatFunc.algEquivOfTranscendental h hh).toAlgHom

omit [CharZero C] [Algebra.EssFiniteType C F] in
@[simp] theorem dependenceRatFuncMap_X (h : F) (hh : Transcendental C h) :
    dependenceRatFuncMap C h hh RatFunc.X = h := by
  change (RatFunc.algEquivOfTranscendental h hh RatFunc.X : F) = h
  exact RatFunc.algEquivOfTranscendental_X h hh

/-- In an essentially finite-type characteristic-zero field extension, a
transcendental element has nonzero actual universal differential. -/
theorem differential_ne_zero_of_transcendental (h : F) (hh : Transcendental C h) :
    KaehlerDifferential.D C F h ≠ 0 := by
  let f := dependenceRatFuncMap C h hh
  letI : Algebra (RatFunc C) F := f.toRingHom.toAlgebra
  letI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (f.commutes c).symm
  letI : Algebra.EssFiniteType (RatFunc C) F :=
    Algebra.EssFiniteType.of_comp C (RatFunc C) F
  have hX : algebraMap (RatFunc C) F RatFunc.X = h := dependenceRatFuncMap_X C h hh
  have ht : (1 : F) ⊗ₜ[RatFunc C]
      KaehlerDifferential.D C (RatFunc C) RatFunc.X ≠ 0 := by
    intro hz
    exact rationalFunction_variable_differential_ne_zero C
      ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (RatFunc C)
        Ω[RatFunc C⁄C] _).mp hz)
  have hi := differential_baseChange_injective C (RatFunc C) F
  have hm : KaehlerDifferential.mapBaseChange C (RatFunc C) F
      ((1 : F) ⊗ₜ[RatFunc C] KaehlerDifferential.D C (RatFunc C) RatFunc.X) ≠ 0 := by
    intro hz
    apply ht
    apply hi
    simpa using hz
  simpa [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hX] using hm

/-- Actual differential vanishing detects algebraicity in the precise
finite-type characteristic-zero setting. -/
theorem differential_eq_zero_iff_isAlgebraic (h : F) :
    KaehlerDifferential.D C F h = 0 ↔ IsAlgebraic C h := by
  constructor
  · intro hd
    by_contra ha
    exact differential_ne_zero_of_transcendental C h ha hd
  · exact relative_differential_eq_zero_of_isAlgebraic h

/-- Equivalent nonvanishing formulation. -/
theorem differential_ne_zero_iff_transcendental (h : F) :
    KaehlerDifferential.D C F h ≠ 0 ↔ Transcendental C h := by
  exact not_congr (differential_eq_zero_iff_isAlgebraic C h)

/-- The nonconstant-function entrance to the curve construction, with the
actual image of the algebraically closed base field made explicit. -/
theorem differential_ne_zero_iff_not_mem_base [IsAlgClosed C] (h : F) :
    KaehlerDifferential.D C F h ≠ 0 ↔ h ∉ Set.range (algebraMap C F) := by
  constructor
  · intro hd hm
    obtain ⟨c, rfl⟩ := hm
    exact hd ((KaehlerDifferential.D C F).map_algebraMap c)
  · intro hn
    exact differential_ne_zero_of_transcendental C h
      (transcendental_of_not_mem_base C h hn)

end FiniteTypeField

section ExteriorContraction

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

/-- The actual exterior contraction associated to a linear functional. -/
def dependenceContractionAlternating (f : E →ₗ[k] k) : E [⋀^Fin 2]→ₗ[k] E where
  toFun a := f (a 0) • a 1 - f (a 1) • a 0
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add, add_smul, smul_add] <;> abel
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul, smul_sub, smul_smul, mul_comm]
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change f (a 0) • a 1 - f (a 1) • a 0 = 0
      simp only [h, sub_self]
    · change a 1 = a 0 at h
      change f (a 0) • a 1 - f (a 1) • a 0 = 0
      simp only [h, sub_self]
    · exact (hij rfl).elim

def dependenceContraction (f : E →ₗ[k] k) : (⋀[k]^2 E) →ₗ[k] E :=
  exteriorPower.alternatingMapLinearEquiv (dependenceContractionAlternating f)

@[simp] theorem dependenceContraction_wedge (f : E →ₗ[k] k) (x y : E) :
    dependenceContraction f (exteriorWedge x y) = f x • y - f y • x := by
  simp [dependenceContraction, exteriorWedge, dependenceContractionAlternating]

/-- Wedge vanishing with a nonzero first vector implies genuine linear
dependence.  A normalized dual functional is constructed, not assumed. -/
theorem scalar_multiple_of_exteriorWedge_eq_zero {x y : E}
    (hx : x ≠ 0) (hxy : exteriorWedge (k := k) x y = 0) : ∃ c : k, y = c • x := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hx
  have h := congrArg (dependenceContraction f) hxy
  refine ⟨f y, ?_⟩
  simpa only [dependenceContraction_wedge, hf, one_smul, map_zero, sub_eq_zero] using h

end ExteriorContraction

section CurveDependence

variable (C : Type*) [Field C] [CharZero C]
variable {F : Type*} [Field F] [Algebra C F] [Algebra.EssFiniteType C F]

/-- The function-field dependence step used in the curve-from-closed-forms
lemma: if `h` is transcendental and `dh ∧ da = 0`, then `a` is algebraic over
the actual intermediate field `C(h)`. -/
theorem isAlgebraic_over_adjoin_of_differential_wedge_eq_zero
    (h a : F) (hh : Transcendental C h)
    (hwa : exteriorWedge (k := F) (KaehlerDifferential.D C F h)
      (KaehlerDifferential.D C F a) = 0) :
    IsAlgebraic (IntermediateField.adjoin C {h}) a := by
  obtain ⟨c, hca⟩ := scalar_multiple_of_exteriorWedge_eq_zero
    (differential_ne_zero_of_transcendental C h hh) hwa
  let L := IntermediateField.adjoin C {h}
  let hL : L := ⟨h, IntermediateField.subset_adjoin C {h} (by simp)⟩
  letI : Algebra.EssFiniteType L F := Algebra.EssFiniteType.of_comp C L F
  have hhrel : KaehlerDifferential.D L F h = 0 := by
    change KaehlerDifferential.D L F (algebraMap L F hL) = 0
    exact (KaehlerDifferential.D L F).map_algebraMap hL
  have harel : KaehlerDifferential.D L F a = 0 := by
    have hm := congrArg (KaehlerDifferential.map C L F F) hca
    simpa [KaehlerDifferential.map_D, hhrel] using hm
  exact (differential_eq_zero_iff_isAlgebraic L a).mp harel

end CurveDependence

section CoefficientField

variable (C : Type*) [Field C]
variable {F : Type*} [Field F] [Algebra C F] {ι : Type*}

/-- The actual coefficient field `C(h,a,bᵢ)`, first viewed as an
intermediate field over `C(h)`.  No algebraicity or dimension is inserted
in this definition. -/
def curveCoefficientField (h a : F) (b : ι → F) :
    IntermediateField (IntermediateField.adjoin C {h}) F :=
  IntermediateField.adjoin (IntermediateField.adjoin C {h}) ({a} ∪ Set.range b)

/-- The actual nested-field algebra structures commute with their
inclusion in the ambient field. -/
instance curveCoefficientField_scalarTower (h a : F) (b : ι → F) :
    IsScalarTower C (curveCoefficientField C h a b) F :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Restricting the scalar field identifies this actual nested adjoin
with the single adjoin `C(h,a,bᵢ)` in the ambient field. -/
theorem curveCoefficientField_restrictScalars_eq (h a : F) (b : ι → F) :
    (curveCoefficientField C h a b).restrictScalars C =
      IntermediateField.adjoin C ({h} ∪ ({a} ∪ Set.range b)) :=
  IntermediateField.adjoin_adjoin_left C {h} ({a} ∪ Set.range b)

theorem curveCoefficientField_mem_h (h a : F) (b : ι → F) :
    h ∈ curveCoefficientField C h a b := by
  exact (curveCoefficientField C h a b).algebraMap_mem
    ⟨h, IntermediateField.subset_adjoin C {h} (by simp)⟩

theorem curveCoefficientField_mem_a (h a : F) (b : ι → F) :
    a ∈ curveCoefficientField C h a b := by
  exact IntermediateField.subset_adjoin (IntermediateField.adjoin C {h})
    ({a} ∪ Set.range b) (Or.inl (by simp))

theorem curveCoefficientField_mem_b (h a : F) (b : ι → F) (i : ι) :
    b i ∈ curveCoefficientField C h a b := by
  exact IntermediateField.subset_adjoin (IntermediateField.adjoin C {h})
    ({a} ∪ Set.range b) (Or.inr ⟨i, rfl⟩)

/-- Each coefficient form is the image of a single actual differential
of the coefficient field; no ambient-field span replaces this image. -/
theorem curveCoefficientField_form_mem_map_range
    (h a : F) (b : ι → F) (i : ι) :
    (a * b i) • KaehlerDifferential.D C F h ∈
      LinearMap.range (KaehlerDifferential.map C C
        (curveCoefficientField C h a b) F) := by
  let L := curveCoefficientField C h a b
  let hL : L := ⟨h, curveCoefficientField_mem_h C h a b⟩
  let aL : L := ⟨a, curveCoefficientField_mem_a C h a b⟩
  let bL : L := ⟨b i, curveCoefficientField_mem_b C h a b i⟩
  exact differential_coefficient_mem_map_range C L F (aL * bL) hL

/-- The corresponding tensor base-change image, with first tensor factor
one and the same actual differential as witness. -/
theorem curveCoefficientField_form_mem_baseChange_range
    (h a : F) (b : ι → F) (i : ι) :
    (a * b i) • KaehlerDifferential.D C F h ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange C
        (curveCoefficientField C h a b) F) := by
  obtain ⟨ω, hω⟩ := curveCoefficientField_form_mem_map_range C h a b i
  refine ⟨(1 : F) ⊗ₜ[curveCoefficientField C h a b] ω, ?_⟩
  simpa only [KaehlerDifferential.mapBaseChange_tmul, one_smul] using hω

/-- For the finite family occurring in the closed-forms curve lemma, the
actual coefficient field is finite over `C(h)`.  Its generators are proved
algebraic using the actual wedge criterion above. -/
theorem curveCoefficientField_finiteDimensional [CharZero C]
    [Algebra.EssFiniteType C F] [Finite ι] (h a : F) (b : ι → F)
    (hh : Transcendental C h)
    (hda : exteriorWedge (k := F) (KaehlerDifferential.D C F h)
      (KaehlerDifferential.D C F a) = 0)
    (hdb : ∀ i, exteriorWedge (k := F) (KaehlerDifferential.D C F h)
      (KaehlerDifferential.D C F (b i)) = 0) :
    FiniteDimensional (IntermediateField.adjoin C {h})
      (curveCoefficientField C h a b) := by
  classical
  letI : Finite ({a} ∪ Set.range b : Set F) :=
    ((Set.finite_singleton a).union (Set.finite_range b)).to_subtype
  apply IntermediateField.finiteDimensional_adjoin
    (S := ({a} ∪ Set.range b : Set F))
  intro x hx
  rcases hx with hx | ⟨i, rfl⟩
  · have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact (isAlgebraic_over_adjoin_of_differential_wedge_eq_zero C h a hh hda).isIntegral
  · exact (isAlgebraic_over_adjoin_of_differential_wedge_eq_zero C h (b i) hh
      (hdb i)).isIntegral

end CoefficientField

end ChenRanks
