import ChenRanks.KoszulIsotropicComponentLocalScalars
import ChenRanks.QuotientLocalizationComparison

/-!
# Genuine scalar algebras and mapped denominators of a component

Every algebra below is induced by an already constructed actual ring
homomorphism: dual-restriction on symmetric algebras, its composition
with actual component localization, and the actual local coefficient
projection. The scalar squares and localization properties are derived
from the proved actual evaluation compatibility and actual section.
No pushout or tensor comparison is a premise.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]
variable (P : Submodule k E)

/-- The real symmetric-algebra projection is surjective by its proved
actual section equation. -/
theorem componentSymmetricProjection_surjective :
    Function.Surjective (componentSymmetricProjection k E P) := by
  intro t
  refine ⟨componentSymmetricSection k E P t, ?_⟩
  exact DFunLike.congr_fun (componentSymmetricProjection_comp_section k E P) t

/-- The actual component symmetric algebra is an ambient coefficient
algebra by its actual dual-restriction homomorphism. -/
@[implicit_reducible] def componentSymmetricProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  (componentSymmetricProjection k E P).toRingHom.toAlgebra

/-- The ambient-to-component-local algebra map is the actual composed
projection and localization map. -/
@[implicit_reducible] def componentPointAmbientCoefficientAlgebra (eP : P) :
    Algebra (S k (_root_.Module.Dual k E)) (componentPointLocalRing k E P eP) :=
  ((algebraMap (S k (_root_.Module.Dual k P)) (componentPointLocalRing k E P eP)).comp
    (componentSymmetricProjection k E P).toRingHom).toAlgebra

/-- The actual local component coefficient ring is an algebra over
the actual ambient local coefficient ring via the actual projection. -/
@[implicit_reducible] def componentPointLocalProjectionAlgebra (eP : P) :
    Algebra (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP) :=
  (componentLocalScalarProjection k E P eP).toAlgebra

local instance componentProjectionAlgebra :
    Algebra (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P)) :=
  componentSymmetricProjectionAlgebra k E P

local instance componentPointAmbientAlgebra (eP : P) :
    Algebra (S k (_root_.Module.Dual k E)) (componentPointLocalRing k E P eP) :=
  componentPointAmbientCoefficientAlgebra k E P eP

local instance componentPointProjectionAlgebra (eP : P) :
    Algebra (ambientComponentPointLocalRing k E P eP) (componentPointLocalRing k E P eP) :=
  componentPointLocalProjectionAlgebra k E P eP

-- Localization also offers a scalar action obtained by applying the
-- Ore construction to the ambient-to-component action. Here the
-- required action is the actual displayed composed coefficient map.
-- Cache its native Algebra parent explicitly so the tower statements
-- retain that same action throughout their proof and specialization.
local instance (priority := 2000) componentPointAmbientScalarAction (eP : P) :
    SMul (S k (_root_.Module.Dual k E)) (componentPointLocalRing k E P eP) :=
  (componentPointAmbientCoefficientAlgebra k E P eP).toSMul

/-- The component scalar tower is the actual composed coefficient map. -/
@[implicit_reducible] def componentPointAmbientComponentScalarTower (eP : P) :
    IsScalarTower (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
      (componentPointLocalRing k E P eP) :=
  IsScalarTower.of_algebraMap_eq'
    (R := S k (_root_.Module.Dual k E))
    (S := S k (_root_.Module.Dual k P))
    (A := componentPointLocalRing k E P eP) rfl

/-- The ambient-local scalar tower is derived from the already proved
actual localization square. -/
@[implicit_reducible] def componentPointAmbientLocalScalarTower (eP : P) :
    IsScalarTower (S k (_root_.Module.Dual k E)) (ambientComponentPointLocalRing k E P eP)
      (componentPointLocalRing k E P eP) := by
  apply IsScalarTower.of_algebraMap_eq'
    (R := S k (_root_.Module.Dual k E))
    (S := ambientComponentPointLocalRing k E P eP)
    (A := componentPointLocalRing k E P eP)
  apply RingHom.ext
  intro s
  exact (componentLocalScalarProjection_algebraMap k E P eP s).symm

/-- The actual ambient prime-complement submonoid maps onto the actual
component prime-complement submonoid, using proved genuine surjectivity
and proved genuine prime contraction. -/
theorem componentProjectedPrimeCompl_map (eP : P) :
    (pointEvaluationKernel k (_root_.Module.Dual k E)
        (pointOfVector k E (eP : E))).primeCompl.map
      (componentSymmetricProjection k E P).toRingHom =
        (pointEvaluationKernel k (_root_.Module.Dual k P)
          (pointOfVector k P eP)).primeCompl := by
  exact ChenRanks.map_primeComplement_eq_of_surjective
    (S k (_root_.Module.Dual k E)) (S k (_root_.Module.Dual k P))
    (componentSymmetricProjection k E P).toRingHom
    (componentSymmetricProjection_surjective k E P)
    (pointEvaluationKernel k (_root_.Module.Dual k E) (pointOfVector k E (eP : E)))
    (pointEvaluationKernel k (_root_.Module.Dual k P) (pointOfVector k P eP))
    (ambientVectorEvaluationPrime_eq_component_comap k E P eP).symm

/-- The actual component local coefficient ring is the actual
localization at the actual mapped ambient denominators. -/
theorem componentTarget_mappedDenominators_isLocalization (eP : P) :
    IsLocalization
      ((pointEvaluationKernel k (_root_.Module.Dual k E)
        (pointOfVector k E (eP : E))).primeCompl.map
          (componentSymmetricProjection k E P).toRingHom)
      (componentPointLocalRing k E P eP) := by
  rw [componentProjectedPrimeCompl_map k E P eP]
  change IsLocalization.AtPrime
    (Localization.AtPrime (pointEvaluationKernel k (_root_.Module.Dual k P)
      (pointOfVector k P eP)))
    (pointEvaluationKernel k (_root_.Module.Dual k P) (pointOfVector k P eP))
  infer_instance

end ChenRanks.Koszul
