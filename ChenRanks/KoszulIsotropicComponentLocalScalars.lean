import ChenRanks.KoszulIsotropicComponentSection
import ChenRanks.KoszulResonanceSupport
import ChenRanks.KoszulLocalizedTransverse
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Actual evaluation-point local coefficient maps for a component

The coefficient maps are the true symmetric-algebra maps of actual dual
restriction and its derived actual linear section. Evaluations are the
existing pointEvaluation maps of the existing pointOfVector functionals,
and primes are the existing vectorEvaluationPrime objects.

For an actual vector eP in the original subspace, evaluation compatibility
is proved on actual symmetric generators. It proves both genuine prime
comap equalities, and those equalities construct the two actual native
AtPrime.localRingHom maps. Their composite on the component coefficient
ring is the identity by the true symmetric-algebra section equation and
native localization uniqueness. The reverse ring composite is not asserted
to be the identity.

These are affine evaluation-point localizations. They are not defined as
homogeneous Proj stalks. No kernel-comap equation, isotropy, separability,
nonzero-point normalization, local module isomorphism, reducedness,
effective decomposition, or Chen comparison is an input or conclusion.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

/-- The actual symmetric-algebra map of genuine dual restriction. -/
abbrev componentSymmetricProjection :
    S k (_root_.Module.Dual k E) →ₐ[k] S k (_root_.Module.Dual k P) :=
  symmetricMap k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
    (componentDualQuotient k E P)

/-- The actual symmetric-algebra map of the derived genuine linear section. -/
abbrev componentSymmetricSection :
    S k (_root_.Module.Dual k P) →ₐ[k] S k (_root_.Module.Dual k E) :=
  symmetricMap k (_root_.Module.Dual k P) (_root_.Module.Dual k E)
    (componentDualSection k E P)

/-- The true generating-space section gives the true coefficient-algebra
section; the equation is not an input. -/
theorem componentSymmetricProjection_comp_section :
    (componentSymmetricProjection k E P).comp (componentSymmetricSection k E P) =
      AlgHom.id k (S k (_root_.Module.Dual k P)) := by
  change (symmetricMap k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
      (componentDualQuotient k E P)).comp
    (symmetricMap k (_root_.Module.Dual k P) (_root_.Module.Dual k E)
      (componentDualSection k E P)) = AlgHom.id k (S k (_root_.Module.Dual k P))
  rw [symmetricMap_comp, componentDualQuotient_comp_section, symmetricMap_id]

/-- Genuine component evaluation after restriction is genuine ambient
evaluation at the very same original vector. -/
theorem componentPointEvaluation_projection (eP : P) :
    (pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP)).comp
        (componentSymmetricProjection k E P) =
      pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E)) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  change pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP)
      (symmetricMap k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
        (componentDualQuotient k E P) (SymmetricAlgebra.ι k (_root_.Module.Dual k E) v)) =
    pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))
      (SymmetricAlgebra.ι k (_root_.Module.Dual k E) v)
  rw [symmetricMap_ι, pointEvaluation_generator, pointEvaluation_generator]
  rfl

/-- Genuine ambient evaluation after the actual derived section is
genuine component evaluation. This follows from actual dual restriction. -/
theorem componentPointEvaluation_section (eP : P) :
    (pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))).comp
        (componentSymmetricSection k E P) =
      pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP) := by
  apply SymmetricAlgebra.algHom_ext
  ext w
  change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))
      (symmetricMap k (_root_.Module.Dual k P) (_root_.Module.Dual k E)
        (componentDualSection k E P) (SymmetricAlgebra.ι k (_root_.Module.Dual k P) w)) =
    pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP)
      (SymmetricAlgebra.ι k (_root_.Module.Dual k P) w)
  rw [symmetricMap_ι, pointEvaluation_generator, pointEvaluation_generator]
  change (componentDualQuotient k E P (componentDualSection k E P w)) eP = w eP
  exact congrArg (fun f : _root_.Module.Dual k P ↦ f eP)
    (componentDualQuotient_section_apply k E P w)

/-- The actual ambient evaluation prime is derived to be the comap of
the actual component prime under the actual coefficient projection. -/
theorem ambientVectorEvaluationPrime_eq_component_comap (eP : P) :
    (vectorEvaluationPrime k E (eP : E)).asIdeal =
      (vectorEvaluationPrime k P eP).asIdeal.comap
        (componentSymmetricProjection k E P).toRingHom := by
  ext s
  change (pointEvaluation k (_root_.Module.Dual k E)
      (pointOfVector k E (eP : E)) s = 0) ↔
    pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP)
      (componentSymmetricProjection k E P s) = 0
  have hs := DFunLike.congr_fun (componentPointEvaluation_projection k E P eP) s
  change pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP)
      (componentSymmetricProjection k E P s) =
    pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E)) s at hs
  rw [hs]

/-- The actual component prime is derived to be the comap of the
ambient prime under the actual coefficient section. -/
theorem componentVectorEvaluationPrime_eq_ambient_comap (eP : P) :
    (vectorEvaluationPrime k P eP).asIdeal =
      (vectorEvaluationPrime k E (eP : E)).asIdeal.comap
        (componentSymmetricSection k E P).toRingHom := by
  ext s
  change (pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP) s = 0) ↔
    pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))
      (componentSymmetricSection k E P s) = 0
  have hs := DFunLike.congr_fun (componentPointEvaluation_section k E P eP) s
  change pointEvaluation k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))
      (componentSymmetricSection k E P s) =
    pointEvaluation k (_root_.Module.Dual k P) (pointOfVector k P eP) s at hs
  rw [hs]

/-- The existing actual ambient evaluation-point local coefficient ring. -/
abbrev ambientComponentPointLocalRing (eP : P) :=
  PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E (eP : E))

/-- The existing actual component evaluation-point local coefficient ring. -/
abbrev componentPointLocalRing (eP : P) :=
  PointLocalCoefficientRing k (_root_.Module.Dual k P) (pointOfVector k P eP)

/-- The native local coefficient projection, constructed using the proved
actual prime-comap equation. -/
def componentLocalScalarProjection (eP : P) :
    ambientComponentPointLocalRing k E P eP →+* componentPointLocalRing k E P eP :=
  Localization.localRingHom
    (vectorEvaluationPrime k E (eP : E)).asIdeal
    (vectorEvaluationPrime k P eP).asIdeal
    (componentSymmetricProjection k E P).toRingHom
    (ambientVectorEvaluationPrime_eq_component_comap k E P eP)

/-- The native local coefficient section, constructed using the proved
actual reverse prime-comap equation. -/
def componentLocalScalarSection (eP : P) :
    componentPointLocalRing k E P eP →+* ambientComponentPointLocalRing k E P eP :=
  Localization.localRingHom
    (vectorEvaluationPrime k P eP).asIdeal
    (vectorEvaluationPrime k E (eP : E)).asIdeal
    (componentSymmetricSection k E P).toRingHom
    (componentVectorEvaluationPrime_eq_ambient_comap k E P eP)

@[simp] theorem componentLocalScalarProjection_algebraMap (eP : P)
    (s : S k (_root_.Module.Dual k E)) :
    componentLocalScalarProjection k E P eP
        (algebraMap (S k (_root_.Module.Dual k E))
          (ambientComponentPointLocalRing k E P eP) s) =
      algebraMap (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP)
        (componentSymmetricProjection k E P s) :=
  Localization.localRingHom_to_map
    (vectorEvaluationPrime k E (eP : E)).asIdeal
    (vectorEvaluationPrime k P eP).asIdeal
    (componentSymmetricProjection k E P).toRingHom
    (ambientVectorEvaluationPrime_eq_component_comap k E P eP) s

@[simp] theorem componentLocalScalarSection_algebraMap (eP : P)
    (s : S k (_root_.Module.Dual k P)) :
    componentLocalScalarSection k E P eP
        (algebraMap (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP) s) =
      algebraMap (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
        (componentSymmetricSection k E P s) :=
  Localization.localRingHom_to_map
    (vectorEvaluationPrime k P eP).asIdeal
    (vectorEvaluationPrime k E (eP : E)).asIdeal
    (componentSymmetricSection k E P).toRingHom
    (componentVectorEvaluationPrime_eq_ambient_comap k E P eP) s

/-- The actual local coefficient projection preserves the original
base-field scalar maps, by actual tower and coefficient compatibility. -/
@[simp] theorem componentLocalScalarProjection_base (eP : P) (c : k) :
    componentLocalScalarProjection k E P eP
        (algebraMap k (ambientComponentPointLocalRing k E P eP) c) =
      algebraMap k (componentPointLocalRing k E P eP) c := by
  rw [IsScalarTower.algebraMap_apply k (S k (_root_.Module.Dual k E))
    (ambientComponentPointLocalRing k E P eP), componentLocalScalarProjection_algebraMap]
  rw [(componentSymmetricProjection k E P).commutes,
    ← IsScalarTower.algebraMap_apply k (S k (_root_.Module.Dual k P))
      (componentPointLocalRing k E P eP)]

/-- The actual local coefficient section also preserves the original
base-field scalar maps. -/
@[simp] theorem componentLocalScalarSection_base (eP : P) (c : k) :
    componentLocalScalarSection k E P eP
        (algebraMap k (componentPointLocalRing k E P eP) c) =
      algebraMap k (ambientComponentPointLocalRing k E P eP) c := by
  rw [IsScalarTower.algebraMap_apply k (S k (_root_.Module.Dual k P))
    (componentPointLocalRing k E P eP), componentLocalScalarSection_algebraMap]
  rw [(componentSymmetricSection k E P).commutes,
    ← IsScalarTower.algebraMap_apply k (S k (_root_.Module.Dual k E))
      (ambientComponentPointLocalRing k E P eP)]

/-- The forward local coefficient map composed with its actual section
is the identity. The reverse ring composition is not asserted to be so. -/
theorem componentLocalScalarProjection_comp_section (eP : P) :
    (componentLocalScalarProjection k E P eP).comp
        (componentLocalScalarSection k E P eP) =
      RingHom.id (componentPointLocalRing k E P eP) := by
  letI : IsLocalization ((vectorEvaluationPrime k P eP).asIdeal.primeCompl)
      (componentPointLocalRing k E P eP) := by
    change IsLocalization
      (pointEvaluationKernel k (_root_.Module.Dual k P) (pointOfVector k P eP)).primeCompl
      (Localization.AtPrime
        (pointEvaluationKernel k (_root_.Module.Dual k P) (pointOfVector k P eP)))
    infer_instance
  apply IsLocalization.ringHom_ext ((vectorEvaluationPrime k P eP).asIdeal.primeCompl)
  apply RingHom.ext
  intro s
  change componentLocalScalarProjection k E P eP
      (componentLocalScalarSection k E P eP
        (algebraMap (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP) s)) =
    algebraMap (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP) s
  rw [componentLocalScalarSection_algebraMap, componentLocalScalarProjection_algebraMap,
    ← AlgHom.comp_apply, componentSymmetricProjection_comp_section, AlgHom.id_apply]

@[simp] theorem componentLocalScalarProjection_section_apply (eP : P)
    (a : componentPointLocalRing k E P eP) :
    componentLocalScalarProjection k E P eP (componentLocalScalarSection k E P eP a) = a :=
  DFunLike.congr_fun (componentLocalScalarProjection_comp_section k E P eP) a

/-- The native local coefficient projection is genuinely surjective. -/
theorem componentLocalScalarProjection_surjective (eP : P) :
    Function.Surjective (componentLocalScalarProjection k E P eP) := by
  intro a
  exact ⟨componentLocalScalarSection k E P eP a,
    componentLocalScalarProjection_section_apply k E P eP a⟩

end ChenRanks.Koszul
