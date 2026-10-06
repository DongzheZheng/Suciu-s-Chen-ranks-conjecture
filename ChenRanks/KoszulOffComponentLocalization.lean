import ChenRanks.KoszulComponentScalarModuleComparison
import ChenRanks.LocalizedTensorVanishing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Literal component localization away from the actual subspace

If an actual vector lies outside an actual subspace, genuine linear
duality constructs a coordinate vanishing on the subspace and nonzero
at that vector. Its actual symmetric image kills the whole original
restricted component quotient. The same actual coordinate is a genuine
denominator at that evaluation prime, so native tensor localization is
zero. This is not a point-fibre or expected-component replacement.
-/

noncomputable section

open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

local instance offComponentProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  componentSymmetricProjectionAlgebra k E P

local instance (priority := 2000) offComponentRestrictedAddCommGroup :
    AddCommGroup (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommGroup k E P

local instance (priority := 2000) offComponentRestrictedAddCommMonoid :
    AddCommMonoid (ComponentAmbientModule k E P) :=
  componentAmbientModuleAddCommMonoid k E P

local instance (priority := 2000) offComponentRestrictedZero :
    Zero (ComponentAmbientModule k E P) :=
  (componentAmbientModuleAddCommMonoid k E P).toZero

local instance (priority := 2000) offComponentRestrictedOriginalCoefficients :
    _root_.Module (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalCoefficients k E P

local instance (priority := 2000) offComponentRestrictedCoefficients :
    _root_.Module (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleCoefficients k E P

local instance (priority := 2000) offComponentRestrictedOriginalScalarAction :
    SMul (S k (_root_.Module.Dual k P)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleOriginalScalarAction k E P

local instance (priority := 2000) offComponentRestrictedScalarAction :
    SMul (S k (_root_.Module.Dual k E)) (ComponentAmbientModule k E P) :=
  componentAmbientModuleScalarAction k E P

/-- Actual dual restriction sends a true annihilator functional to zero. -/
theorem componentDualQuotient_eq_zero_of_annihilator
    (u : _root_.Module.Dual k E) (hu : u ∈ P.dualAnnihilator) :
    componentDualQuotient k E P u = 0 := by
  apply LinearMap.ext
  intro p
  change u (p : E) = 0
  exact (Submodule.mem_dualAnnihilator (W := P) u).mp hu p p.property

/-- A genuine annihilator coordinate kills every class in the same
original zero-relation quotient with its actual ambient action. -/
theorem componentAmbientModule_annihilatorCoordinate_smul
    (u : _root_.Module.Dual k E) (hu : u ∈ P.dualAnnihilator)
    (z : ComponentAmbientModule k E P) :
    SymmetricAlgebra.ι k (_root_.Module.Dual k E) u • z = 0 := by
  change componentSymmetricProjection k E P
      (SymmetricAlgebra.ι k (_root_.Module.Dual k E) u) • z = 0
  rw [symmetricMap_ι, componentDualQuotient_eq_zero_of_annihilator k E P u hu,
    map_zero, zero_smul]

/-- Genuine duality constructs the separating coordinate; it is not
supplied as a detector or annihilating-module premise. -/
theorem exists_componentAnnihilator_nonzero_at_point (e : E) (he : e ∉ P) :
    ∃ u : _root_.Module.Dual k E, u ∈ P.dualAnnihilator ∧ u e ≠ 0 := by
  classical
  have hnot : ¬ ∀ u : _root_.Module.Dual k E, u ∈ P.dualAnnihilator → u e = 0 := by
    intro h
    exact he ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff P e).mp h)
  obtain ⟨u, hu⟩ := not_forall.mp hnot
  exact ⟨u, (_root_.not_imp.mp hu).1, (_root_.not_imp.mp hu).2⟩

/-- At a genuine point outside the actual subspace, the literal tensor
localization of the original restricted component module is zero. -/
theorem componentAmbientModule_localization_eq_zero_of_not_mem
    (e : E) (he : e ∉ P)
    (z : PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
      ⊗[S k (_root_.Module.Dual k E)] ComponentAmbientModule k E P) : z = 0 := by
  obtain ⟨u, hu, hue⟩ := exists_componentAnnihilator_nonzero_at_point k E P e he
  apply ChenRanks.localizedTensor_eq_zero_of_annihilating_denominator
    (S k (_root_.Module.Dual k E))
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
    (pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E e)).primeCompl
    (ComponentAmbientModule k E P) (SymmetricAlgebra.ι k (_root_.Module.Dual k E) u)
    ?_ (componentAmbientModule_annihilatorCoordinate_smul k E P u hu) z
  change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E e)
    (SymmetricAlgebra.ι k (_root_.Module.Dual k E) u) ≠ 0
  rw [pointEvaluation_generator]
  exact hue

/-- The vanishing holds for the whole actual tensor module, without
isotropy, finite dimension, or characteristic-zero assumptions. -/
theorem componentAmbientModule_localization_subsingleton_of_not_mem
    (e : E) (he : e ∉ P) :
    Subsingleton (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
      ⊗[S k (_root_.Module.Dual k E)] ComponentAmbientModule k E P) := by
  refine ⟨fun z t => ?_⟩
  exact (componentAmbientModule_localization_eq_zero_of_not_mem k E P e he z).trans
    (componentAmbientModule_localization_eq_zero_of_not_mem k E P e he t).symm

end ChenRanks.Koszul
