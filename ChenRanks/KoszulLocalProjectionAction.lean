import ChenRanks.KoszulIsotropicComponentLocalScalars
import ChenRanks.KoszulLocalizedAnnihilator
import Mathlib.Algebra.Module.End

/-!
# True local scalar action of the actual component projection

Dual restriction and its derived section determine a genuine projection
on the original dual generating space. Its difference from the identity
belongs to the ordinary annihilator of the actual subspace. Separation
already proves that every such transverse coordinate annihilates the
whole literal localized original Koszul module.

The generator equality is extended to every true symmetric polynomial
by native symmetric-algebra induction, then to every true localized
coefficient by the localization universal property applied to the
actual additive-endomorphism representation of the scalar action.
No faithful action, free module, local isomorphism, or scalar-action
equality is assumed. The rings here remain affine evaluation-point
localizations; no identification with Proj stalks is asserted.
-/

noncomputable section

namespace ChenRanks.Koszul

private theorem scalar_action_eq_of_sub_action_zero
    (R N : Type*) [CommRing R] [AddCommGroup N] [_root_.Module R N]
    (r s : R) (z : N) (h : (r - s) • z = 0) : r • z = s • z := by
  rw [sub_smul] at h
  exact sub_eq_zero.mp h

private theorem symmetric_scalar_action_ext
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (R : Type*) [CommRing R] (μ : S k V →+* R)
    (N : Type*) [AddCommGroup N] [_root_.Module R N]
    (F : S k V →ₐ[k] S k V)
    (hι : ∀ (v : V) (z : N), μ (F (SymmetricAlgebra.ι k V v)) • z =
      μ (SymmetricAlgebra.ι k V v) • z) :
    ∀ (s : S k V) (z : N), μ (F s) • z = μ s • z := by
  intro s
  induction s using SymmetricAlgebra.induction with
  | algebraMap c =>
      intro z
      rw [F.commutes]
  | ι v => exact hι v
  | mul s t hs ht =>
      intro z
      rw [map_mul, map_mul, map_mul, mul_smul, mul_smul, ht, hs]
  | add s t hs ht =>
      intro z
      rw [map_add, map_add, map_add, add_smul, add_smul, hs, ht]

private theorem localization_scalar_action_ext
    (S R : Type*) [CommRing S] [CommRing R] [Algebra S R]
    (D : Submonoid S) [IsLocalization D R]
    (N : Type*) [AddCommGroup N] [_root_.Module R N]
    (η : R →+* R)
    (hbase : ∀ (s : S) (z : N), η (algebraMap S R s) • z = algebraMap S R s • z) :
    ∀ (r : R) (z : N), η r • z = r • z := by
  have hhom : (_root_.Module.toAddMonoidEnd R N).comp η =
      _root_.Module.toAddMonoidEnd R N := by
    apply IsLocalization.ringHom_ext D
    apply RingHom.ext
    intro s
    apply AddMonoidHom.ext
    intro z
    exact hbase s z
  intro r z
  exact congrArg (fun f : AddMonoid.End N ↦ f z) (DFunLike.congr_fun hhom r)

variable (k : Type*) [Field k]

local instance projectionOriginalAddCommGroup
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : AddCommGroup (Module k V K) :=
  originalModuleAddCommGroup k V K

@[implicit_reducible] private def projectionOriginalCoefficientModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  inferInstance

local instance projectionOriginalCoefficients
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) : _root_.Module (S k V) (Module k V K) :=
  projectionOriginalCoefficientModule k V K

@[implicit_reducible] private def projectionExtendedNativeModule
    (V : Type*) [AddCommGroup V] [_root_.Module k V]
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R] :
    _root_.Module R (CoefficientExtendedModule k V K R) := inferInstance

variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

/-- The genuine dual-space projection built from actual restriction and
its derived actual section. -/
abbrev componentDualProjection : _root_.Module.Dual k E →ₗ[k] _root_.Module.Dual k E :=
  (componentDualSection k E P).comp (componentDualQuotient k E P)

/-- Projection changes an original functional by a genuine transverse
functional. This is derived by evaluating actual dual restriction. -/
theorem componentDualProjection_sub_mem_annihilator (x : _root_.Module.Dual k E) :
    componentDualProjection k E P x - x ∈ P.dualAnnihilator := by
  apply (Submodule.mem_dualAnnihilator (W := P) _).mpr
  intro e he
  have h := congrArg (fun f : _root_.Module.Dual k P ↦ f ⟨e, he⟩)
    (componentDualQuotient_section_apply k E P (componentDualQuotient k E P x))
  change componentDualProjection k E P x e = x e at h
  change componentDualProjection k E P x e - x e = 0
  exact sub_eq_zero.mpr h

/-- The actual coefficient projection followed by its actual section. -/
abbrev componentSymmetricRetraction :
    S k (_root_.Module.Dual k E) →ₐ[k] S k (_root_.Module.Dual k E) :=
  (componentSymmetricSection k E P).comp (componentSymmetricProjection k E P)

/-- The reverse composite of the two genuine local coefficient maps.
It is a ring retraction, and is not defined to be the identity. -/
abbrev componentLocalScalarRetraction (eP : P) :
    ambientComponentPointLocalRing k E P eP →+*
      ambientComponentPointLocalRing k E P eP :=
  (componentLocalScalarSection k E P eP).comp
    (componentLocalScalarProjection k E P eP)

@[simp] theorem componentSymmetricRetraction_generator (x : _root_.Module.Dual k E) :
    componentSymmetricRetraction k E P (SymmetricAlgebra.ι k (_root_.Module.Dual k E) x) =
      SymmetricAlgebra.ι k (_root_.Module.Dual k E) (componentDualProjection k E P x) := by
  change componentSymmetricSection k E P
      (componentSymmetricProjection k E P (SymmetricAlgebra.ι k (_root_.Module.Dual k E) x)) = _
  rw [symmetricMap_ι, symmetricMap_ι]
  rfl

@[simp] theorem componentLocalScalarRetraction_algebraMap (eP : P)
    (s : S k (_root_.Module.Dual k E)) :
    componentLocalScalarRetraction k E P eP
        (algebraMap (S k (_root_.Module.Dual k E))
          (ambientComponentPointLocalRing k E P eP) s) =
      algebraMap (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
        (componentSymmetricRetraction k E P s) := by
  change componentLocalScalarSection k E P eP
    (componentLocalScalarProjection k E P eP (algebraMap _ _ s)) = _
  rw [componentLocalScalarProjection_algebraMap, componentLocalScalarSection_algebraMap]
  rfl

variable (I : Submodule k (⋀[k]^2 E)) [FiniteDimensional k E] [CharZero k]

/-- The actual original quotient localized at the actual ambient
evaluation prime. It is the literal tensor product already used above. -/
abbrev componentPointOriginalModule (eP : P) :=
  CoefficientExtendedModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
    (ambientComponentPointLocalRing k E P eP)

local instance projectionPointNativeModule (eP : P) :
    _root_.Module (ambientComponentPointLocalRing k E P eP)
      (componentPointOriginalModule k E P I eP) :=
  projectionExtendedNativeModule k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
    (ambientComponentPointLocalRing k E P eP)

/-- Separation proves equality of the actual scalar actions of an
original generating functional and its true projected functional. -/
theorem actualPointLocalized_projectedGenerator_action
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (x : _root_.Module.Dual k E) (z : componentPointOriginalModule k E P I eP) :
    extendedCoefficient k (_root_.Module.Dual k E)
        (ambientComponentPointLocalRing k E P eP) (componentDualProjection k E P x) • z =
      extendedCoefficient k (_root_.Module.Dual k E)
        (ambientComponentPointLocalRing k E P eP) x • z := by
  let u : P.dualAnnihilator :=
    ⟨componentDualProjection k E P x - x,
      componentDualProjection_sub_mem_annihilator k E P x⟩
  have hzero := actualPointLocalized_transverseCoordinate_annihilates
    k E P I hsep (eP : E) eP.property v hv u z
  change algebraMap (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
    (SymmetricAlgebra.ι k (_root_.Module.Dual k E) (componentDualProjection k E P x - x)) • z = 0 at hzero
  rw [map_sub, map_sub] at hzero
  exact scalar_action_eq_of_sub_action_zero (ambientComponentPointLocalRing k E P eP)
    (componentPointOriginalModule k E P I eP)
    (extendedCoefficient k (_root_.Module.Dual k E)
      (ambientComponentPointLocalRing k E P eP) (componentDualProjection k E P x))
    (extendedCoefficient k (_root_.Module.Dual k E)
      (ambientComponentPointLocalRing k E P eP) x) z hzero

/-- The actual action equality holds for every original polynomial,
proved by native symmetric-algebra induction from actual whole-module
transverse annihilation. -/
theorem actualPointLocalized_projectedPolynomial_action
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (s : S k (_root_.Module.Dual k E)) (z : componentPointOriginalModule k E P I eP) :
    algebraMap (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
        (componentSymmetricRetraction k E P s) • z =
      algebraMap (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP) s • z := by
  apply symmetric_scalar_action_ext k (_root_.Module.Dual k E)
    (ambientComponentPointLocalRing k E P eP) (algebraMap _ _)
    (componentPointOriginalModule k E P I eP) (componentSymmetricRetraction k E P)
  intro x t
  rw [componentSymmetricRetraction_generator]
  exact actualPointLocalized_projectedGenerator_action k E P I hsep eP v hv x t

/-- The actual reverse coefficient composite acts as the identity on
the entire literal localized original module. This uses localization
uniqueness of the actual scalar representation, not a faithful-action
or freeness hypothesis. -/
theorem actualPointLocalized_retraction_action
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P) (eP : P)
    (v : _root_.Module.Dual k E) (hv : v (eP : E) = 1)
    (r : ambientComponentPointLocalRing k E P eP)
    (z : componentPointOriginalModule k E P I eP) :
    componentLocalScalarRetraction k E P eP r • z = r • z := by
  apply localization_scalar_action_ext (S k (_root_.Module.Dual k E))
    (ambientComponentPointLocalRing k E P eP)
    (pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))).primeCompl
    (componentPointOriginalModule k E P I eP) (componentLocalScalarRetraction k E P eP)
  intro s t
  rw [componentLocalScalarRetraction_algebraMap]
  exact actualPointLocalized_projectedPolynomial_action k E P I hsep eP v hv s t

end ChenRanks.Koszul
