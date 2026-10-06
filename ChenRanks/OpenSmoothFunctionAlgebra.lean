import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic

/-!
# Actual smooth complex-valued functions on a real open set

Functions have the original open set as their domain.  Extension by zero
is used only as an ambient representative of each germ inside that open
set; no global smoothness of the extension is asserted.  The native
Fréchet derivative of this representative defines actual directional
derivations of the smooth-function algebra.  Smoothness of derivatives
and the Leibniz rule are proved from native calculus, not supplied as
fields in a differential algebra structure.
-/

noncomputable section

open scoped ContDiff

open scoped Topology

namespace ChenRanks.OpenSmoothFunctions

local instance smoothFunctionRealComplexContinuousSMul : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    simpa only [RCLike.real_smul_eq_coe_mul] using
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd :
        Continuous fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extension by zero, used only to calculate germs on the actual open set. -/
def zeroExtension (U : TopologicalSpace.Opens E) (f : U → ℂ) (x : E) : ℂ := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 0

@[simp] theorem zeroExtension_apply_mem (U : TopologicalSpace.Opens E)
    (f : U → ℂ) (x : E) (hx : x ∈ U) :
    zeroExtension U f x = f ⟨x, hx⟩ := by
  classical
  simp [zeroExtension, hx]

@[simp] theorem zeroExtension_apply_coe (U : TopologicalSpace.Opens E)
    (f : U → ℂ) (x : U) : zeroExtension U f x.val = f x :=
  zeroExtension_apply_mem U f x.val x.property

theorem zeroExtension_add (U : TopologicalSpace.Opens E) (f g : U → ℂ) :
    zeroExtension U (f + g) = fun x => zeroExtension U f x + zeroExtension U g x := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [zeroExtension, hx]

theorem zeroExtension_mul (U : TopologicalSpace.Opens E) (f g : U → ℂ) :
    zeroExtension U (f * g) = fun x => zeroExtension U f x * zeroExtension U g x := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [zeroExtension, hx]

theorem zeroExtension_smul (U : TopologicalSpace.Opens E) (c : ℂ) (f : U → ℂ) :
    zeroExtension U (c • f) = fun x => c • zeroExtension U f x := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [zeroExtension, hx]

/-- The genuine algebra of smooth complex-valued functions on `U`. -/
def algebra (U : TopologicalSpace.Opens E) : Subalgebra ℂ (U → ℂ) where
  carrier := {f | ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U f) U}
  zero_mem' := by
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U 0) U
    apply (show ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun _ : E => (0 : ℂ)) U from
      contDiff_const.contDiffOn).congr
    intro x hx
    simp only [zeroExtension_apply_mem U 0 x hx, Pi.zero_apply]
  one_mem' := by
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U 1) U
    apply (show ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun _ : E => (1 : ℂ)) U from
      contDiff_const.contDiffOn).congr
    intro x hx
    simp only [zeroExtension_apply_mem U 1 x hx, Pi.one_apply]
  add_mem' := by
    intro f g hf hg
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U (f + g)) U
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U f) U at hf
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U g) U at hg
    rw [zeroExtension_add]
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U (f * g)) U
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U f) U at hf
    change ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U g) U at hg
    rw [zeroExtension_mul]
    exact hf.mul hg
  algebraMap_mem' := by
    intro c
    change ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (zeroExtension U (algebraMap ℂ (U → ℂ) c)) U
    apply (show ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun _ : E => c) U from
      contDiff_const.contDiffOn).congr
    intro x hx
    simp only [zeroExtension_apply_mem U (algebraMap ℂ (U → ℂ) c) x hx,
      Pi.algebraMap_apply, Algebra.algebraMap_self]
    rfl

/-- Native subalgebra carrier; its ring and complex algebra structures are
the actual pointwise ones. -/
abbrev SmoothFunction (U : TopologicalSpace.Opens E) := ↥(algebra U)

instance smoothFunctionCoeFun (U : TopologicalSpace.Opens E) :
    CoeFun (SmoothFunction U) (fun _ => U → ℂ) := ⟨fun f => f.val⟩

theorem smooth_zeroExtension (U : TopologicalSpace.Opens E) (f : SmoothFunction U) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (zeroExtension U f.val) U := by
  simpa only [algebra, Set.mem_setOf_eq] using f.property

theorem differentiable_zeroExtension_at
    (U : TopologicalSpace.Opens E) (f : SmoothFunction U) (x : U) :
    DifferentiableAt ℝ (zeroExtension U f.val) x.val :=
  (smooth_zeroExtension U f).contDiffAt (U.isOpen.mem_nhds x.property)
    |>.differentiableAt (by simp)

/-- Actual derivative along an ambient tangent vector. -/
def directionalValue (U : TopologicalSpace.Opens E) (v : E)
    (f : SmoothFunction U) (x : U) : ℂ :=
  fderiv ℝ (zeroExtension U f.val) x.val v

/-- Actual native derivative smoothness on an open set, followed by real
continuous-linear evaluation, proves this is again a smooth function. -/
theorem directionalValue_mem (U : TopologicalSpace.Opens E) (v : E)
    (f : SmoothFunction U) : directionalValue U v f ∈ algebra U := by
  change ContDiffOn ℝ (∞ : WithTop ℕ∞)
    (zeroExtension U (directionalValue U v f)) U
  have hd : ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fderiv ℝ (zeroExtension U f.val)) U :=
    (smooth_zeroExtension U f).fderiv_of_isOpen U.isOpen (by simp)
  have he : ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun x => fderiv ℝ (zeroExtension U f.val) x v) U :=
    hd.clm_apply contDiff_const.contDiffOn
  apply he.congr
  intro x hx
  exact zeroExtension_apply_mem U (directionalValue U v f) x hx

/-- The actual derivative as a smooth function on the original open set. -/
def directional (U : TopologicalSpace.Opens E) (v : E) (f : SmoothFunction U) : SmoothFunction U :=
  ⟨directionalValue U v f, directionalValue_mem U v f⟩

@[simp] theorem directional_apply (U : TopologicalSpace.Opens E) (v : E)
    (f : SmoothFunction U) (x : U) :
    directional U v f x = fderiv ℝ (zeroExtension U f.val) x.val v := rfl

/-- Real calculus gives a genuinely complex-linear operator on the actual
complex-valued smooth-function algebra. -/
def directionalLinearMap (U : TopologicalSpace.Opens E) (v : E) :
    SmoothFunction U →ₗ[ℂ] SmoothFunction U where
  toFun := directional U v
  map_add' f g := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (zeroExtension U (f.val + g.val)) x.val v =
      fderiv ℝ (zeroExtension U f.val) x.val v +
        fderiv ℝ (zeroExtension U g.val) x.val v
    rw [zeroExtension_add,
      fderiv_fun_add (differentiable_zeroExtension_at U f x)
        (differentiable_zeroExtension_at U g x), ContinuousLinearMap.add_apply]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (zeroExtension U (c • f.val)) x.val v =
      c • fderiv ℝ (zeroExtension U f.val) x.val v
    rw [zeroExtension_smul,
      fderiv_fun_const_smul (differentiable_zeroExtension_at U f x) c,
      ContinuousLinearMap.smul_apply]

/-- Native multiplication differentiation proves the Leibniz rule for
actual original-domain functions. -/
theorem directionalLinearMap_leibniz (U : TopologicalSpace.Opens E) (v : E)
    (f g : SmoothFunction U) :
    directionalLinearMap U v (f * g) =
      f * directionalLinearMap U v g + g * directionalLinearMap U v f := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (zeroExtension U (f.val * g.val)) x.val v =
    f x * fderiv ℝ (zeroExtension U g.val) x.val v +
      g x * fderiv ℝ (zeroExtension U f.val) x.val v
  rw [zeroExtension_mul]
  have hm := congrArg (fun D : E →L[ℝ] ℂ => D v)
    (((differentiable_zeroExtension_at U f x).hasFDerivAt.mul
      (differentiable_zeroExtension_at U g x).hasFDerivAt).fderiv)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    zeroExtension_apply_coe, smul_eq_mul] using hm

/-- A true native derivation, whose differential operator and Leibniz rule
were both constructed and proved from calculus above. -/
def directionalDerivation (U : TopologicalSpace.Opens E) (v : E) :
    Derivation ℂ (SmoothFunction U) (SmoothFunction U) :=
  Derivation.mk' (directionalLinearMap U v) (by
    intro f g
    simpa only [smul_eq_mul] using directionalLinearMap_leibniz U v f g)

@[simp] theorem directionalDerivation_apply
    (U : TopologicalSpace.Opens E) (v : E) (f : SmoothFunction U) (x : U) :
    directionalDerivation U v f x = fderiv ℝ (zeroExtension U f.val) x.val v := rfl

end ChenRanks.OpenSmoothFunctions
