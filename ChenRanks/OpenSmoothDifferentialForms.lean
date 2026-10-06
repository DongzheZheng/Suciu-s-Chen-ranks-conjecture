import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Complex.Basic

/-!
# Actual smooth forms and their square-zero exterior derivative

The domain is an actual open subset of the original real normed space.
Forms are actual complex-valued continuous alternating maps, evaluated on
the original tangent vectors.  Zero extension is only an ambient germ
representative on that open subset.  Native calculus proves smoothness,
complex linearity, locality, and square zero of the exterior derivative.
No differential-complex, closedness, or comparison premise is supplied.
This file constructs a cochain complex; wedge multiplication and its
Leibniz rule, a de Rham comparison, and formality are separate obligations.
-/

noncomputable section


open scoped Topology
open ContinuousAlternatingMap

namespace ChenRanks.OpenSmoothForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two scalar actions act on the actual complex values of a form. -/
local instance realComplexFormScalarTower (n : ℕ) :
    IsScalarTower ℝ ℂ (E [⋀^Fin n]→L[ℝ] ℂ) where
  smul_assoc a c ω := by
    ext v
    exact smul_assoc a c (ω v)

/-- Extension only for calculating the germs of actual forms on `U`. -/
def zeroExtension (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : U → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) : E [⋀^Fin n]→L[ℝ] ℂ := by
  classical
  exact if hx : x ∈ U then ω ⟨x, hx⟩ else 0

@[simp] theorem zeroExtension_apply_mem
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : U → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) (hx : x ∈ U) :
    zeroExtension U n ω x = ω ⟨x, hx⟩ := by
  classical
  simp [zeroExtension, hx]

@[simp] theorem zeroExtension_apply_coe
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : U → E [⋀^Fin n]→L[ℝ] ℂ) (x : U) :
    zeroExtension U n ω x.val = ω x :=
  zeroExtension_apply_mem U n ω x.val x.property

theorem zeroExtension_add
    (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω η : U → E [⋀^Fin n]→L[ℝ] ℂ) :
    zeroExtension U n (ω + η) = fun x =>
      zeroExtension U n ω x + zeroExtension U n η x := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [zeroExtension, hx]

theorem zeroExtension_smul
    (U : TopologicalSpace.Opens E) (n : ℕ) (c : ℂ)
    (ω : U → E [⋀^Fin n]→L[ℝ] ℂ) :
    zeroExtension U n (c • ω) = fun x => c • zeroExtension U n ω x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp [zeroExtension, hx]
  · simp only [zeroExtension, dif_neg hx]
    ext v
    change (0 : ℂ) = c * 0
    simp

/-- The genuine smooth submodule of actual forms on the actual open set. -/
def smoothModule (U : TopologicalSpace.Opens E) (n : ℕ) :
    Submodule ℂ (U → E [⋀^Fin n]→L[ℝ] ℂ) where
  carrier := {ω | ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n ω) U}
  zero_mem' := by
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n 0) U
    apply (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : E => (0 : E [⋀^Fin n]→L[ℝ] ℂ)) U from
        contDiff_const.contDiffOn).congr
    intro x hx
    simp only [zeroExtension_apply_mem U n 0 x hx, Pi.zero_apply]
  add_mem' := by
    intro ω η hω hη
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n (ω + η)) U
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n ω) U at hω
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n η) U at hη
    rw [zeroExtension_add]
    exact hω.add hη
  smul_mem' := by
    intro c ω hω
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n (c • ω)) U
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n ω) U at hω
    rw [zeroExtension_smul]
    exact ContDiffOn.const_smul c hω

abbrev SmoothForm (U : TopologicalSpace.Opens E) (n : ℕ) := ↥(smoothModule U n)

instance smoothFormCoeFun (U : TopologicalSpace.Opens E) (n : ℕ) :
    CoeFun (SmoothForm U n) (fun _ => U → E [⋀^Fin n]→L[ℝ] ℂ) := ⟨fun ω => ω.val⟩

theorem smooth_zeroExtension (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : SmoothForm U n) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (zeroExtension U n ω.val) U := by
  simpa only [smoothModule, Set.mem_setOf_eq] using ω.property

theorem differentiable_zeroExtension_at
    (U : TopologicalSpace.Opens E) (n : ℕ) (ω : SmoothForm U n) (x : U) :
    DifferentiableAt ℝ (zeroExtension U n ω.val) x.val :=
  (smooth_zeroExtension U n ω).contDiffAt (U.isOpen.mem_nhds x.property)
    |>.differentiableAt (by simp)

/-- The actual exterior derivative evaluated inside the original domain. -/
def differentialValue (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : SmoothForm U n) (x : U) : E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  extDeriv (zeroExtension U n ω.val) x.val

/-- Actual derivative smoothness followed by the native continuous-linear
alternation proves that exterior differentiation stays in smooth forms. -/
theorem differentialValue_mem (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : SmoothForm U n) : differentialValue U n ω ∈ smoothModule U (n + 1) := by
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (zeroExtension U (n + 1) (differentialValue U n ω)) U
  have hd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (zeroExtension U n ω.val)) U :=
    (smooth_zeroExtension U n ω).fderiv_of_isOpen U.isOpen (by simp)
  have he : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (extDeriv (zeroExtension U n ω.val)) U := by
    simpa only [extDeriv, alternatizeUncurryFin, Function.comp_def] using
      (alternatizeUncurryFinCLM (n := n) ℝ E ℂ).contDiff.comp_contDiffOn hd
  apply he.congr
  intro x hx
  exact zeroExtension_apply_mem U (n + 1) (differentialValue U n ω) x hx

/-- The native exterior derivative on the actual smooth form module. -/
def differential (U : TopologicalSpace.Opens E) (n : ℕ)
    (ω : SmoothForm U n) : SmoothForm U (n + 1) :=
  ⟨differentialValue U n ω, differentialValue_mem U n ω⟩

@[simp] theorem differential_apply
    (U : TopologicalSpace.Opens E) (n : ℕ) (ω : SmoothForm U n) (x : U) :
    differential U n ω x = extDeriv (zeroExtension U n ω.val) x.val := rfl

/-- Complex scalar linearity is proved for the actual exterior derivative,
whose underlying Fréchet derivative is taken over the real field. -/
def differentialLinearMap (U : TopologicalSpace.Opens E) (n : ℕ) :
    SmoothForm U n →ₗ[ℂ] SmoothForm U (n + 1) where
  toFun := differential U n
  map_add' ω η := by
    apply Subtype.ext
    funext x
    change extDeriv (zeroExtension U n (ω.val + η.val)) x.val = _
    rw [zeroExtension_add]
    exact extDeriv_fun_add (differentiable_zeroExtension_at U n ω x)
      (differentiable_zeroExtension_at U n η x)
  map_smul' c ω := by
    apply Subtype.ext
    funext x
    change extDeriv (zeroExtension U n (c • ω.val)) x.val =
      c • extDeriv (zeroExtension U n ω.val) x.val
    rw [zeroExtension_smul]
    simp only [extDeriv,
      fderiv_fun_const_smul (differentiable_zeroExtension_at U n ω x) c,
      alternatizeUncurryFin_smul]

/-- A genuine neighborhood identity, not a globally smooth extension. -/
theorem zeroExtension_differential_eventuallyEq
    (U : TopologicalSpace.Opens E) (n : ℕ) (ω : SmoothForm U n) (x : U) :
    zeroExtension U (n + 1) (differential U n ω).val =ᶠ[𝓝 x.val]
      extDeriv (zeroExtension U n ω.val) := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  rw [zeroExtension_apply_mem U (n + 1) (differential U n ω).val y hy]
  rfl

/-- Actual square zero, derived from native second-derivative symmetry and
the proved locality of the representative used for the first derivative. -/
theorem differential_squared_eq_zero
    (U : TopologicalSpace.Opens E) (n : ℕ) (ω : SmoothForm U n) :
    differential U (n + 1) (differential U n ω) = 0 := by
  apply Subtype.ext
  funext x
  change extDeriv (zeroExtension U (n + 1) (differential U n ω).val) x.val = 0
  rw [extDeriv, (zeroExtension_differential_eventuallyEq U n ω x).fderiv_eq]
  exact extDeriv_extDeriv_apply
    ((smooth_zeroExtension U n ω).contDiffAt (U.isOpen.mem_nhds x.property))
      (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)

/-- The actual complex-linear operators satisfy the cochain-complex law. -/
theorem differentialLinearMap_comp_eq_zero
    (U : TopologicalSpace.Opens E) (n : ℕ) :
    (differentialLinearMap U (n + 1)).comp (differentialLinearMap U n) = 0 := by
  apply LinearMap.ext
  intro ω
  change differential U (n + 1) (differential U n ω) = 0
  exact differential_squared_eq_zero U n ω

end ChenRanks.OpenSmoothForms
