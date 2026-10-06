import ChenRanks.KoszulProjectiveScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The actual projective quotient map and its point image

The map is the genuine graded quotient map of the actual coefficient
ring by a native homogeneous ideal. Its native Proj morphism has the
actual quotient scheme as source. Its point image is proved to be the
native zero locus of the original ideal, using the true surjective
ideal correspondence. No ground-field point classification, scheme
reducedness, or sheaf-level closed-immersion property is assumed here.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)
variable (H : HomogeneousIdeal (homogeneousS k V b))

/-- The actual quotient homomorphism preserves the actual quotient
degree images by their proved representative description. -/
def homogeneousCoefficientQuotientMap :
    homogeneousS k V b →+*ᵍ quotientCoefficientPiece k V b H where
  toRingHom := Ideal.Quotient.mk H.toIdeal
  map_mem hs := ⟨_, hs, rfl⟩

@[simp] theorem homogeneousCoefficientQuotientMap_apply (s : S k V) :
    homogeneousCoefficientQuotientMap k V b H s = Ideal.Quotient.mk H.toIdeal s := rfl

/-- Genuine quotient surjectivity, without a new existence input. -/
theorem homogeneousCoefficientQuotientMap_surjective :
    Function.Surjective (homogeneousCoefficientQuotientMap k V b H) :=
  Ideal.Quotient.mk_surjective

/-- Every positive quotient degree has an actual positive homogeneous
representative, which proves the native condition for the Proj map. -/
theorem quotient_irrelevant_le_map :
    HomogeneousIdeal.irrelevant (quotientCoefficientPiece k V b H) ≤
      (HomogeneousIdeal.irrelevant (homogeneousS k V b)).map
        (homogeneousCoefficientQuotientMap k V b H) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn q hq
  obtain ⟨s, hs, rfl⟩ := hq
  exact Ideal.mem_map_of_mem (homogeneousCoefficientQuotientMap k V b H)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn hs)

/-- The actual native continuous map of relevant homogeneous primes. -/
def quotientProjectivePointMap :
    ProjectiveSpectrum (quotientCoefficientPiece k V b H) →
      ProjectiveSpectrum (homogeneousS k V b) :=
  AlgebraicGeometry.ProjectiveSpectrum.comapFun
    (homogeneousCoefficientQuotientMap k V b H) (quotient_irrelevant_le_map k V b H)

/-- The actual Proj scheme morphism induced by the true quotient map. -/
def homogeneousCoefficientProjMap :
    AlgebraicGeometry.Proj (quotientCoefficientPiece k V b H) ⟶
      AlgebraicGeometry.Proj (homogeneousS k V b) :=
  AlgebraicGeometry.Proj.map (homogeneousCoefficientQuotientMap k V b H)
    (quotient_irrelevant_le_map k V b H)

/-- The true ideal map-comap identity above the actual quotient kernel. -/
theorem quotient_comap_map (P : HomogeneousIdeal (homogeneousS k V b))
    (hH : H ≤ P) :
    (P.map (homogeneousCoefficientQuotientMap k V b H)).comap
        (homogeneousCoefficientQuotientMap k V b H) = P := by
  apply HomogeneousIdeal.ext
  change Ideal.comap (Ideal.Quotient.mk H.toIdeal)
    (Ideal.map (Ideal.Quotient.mk H.toIdeal) P.toIdeal) = P.toIdeal
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr (show H.toIdeal ≤ P.toIdeal from hH)

/-- A genuine relevant prime containing the actual quotient ideal gives
a genuine relevant prime in the actual quotient ring. -/
def quotientProjectivePointLift (p : ProjectiveSpectrum (homogeneousS k V b))
    (hH : H ≤ p.asHomogeneousIdeal) :
    ProjectiveSpectrum (quotientCoefficientPiece k V b H) where
  asHomogeneousIdeal := p.asHomogeneousIdeal.map (homogeneousCoefficientQuotientMap k V b H)
  isPrime := by
    apply Ideal.map_isPrime_of_surjective
      (homogeneousCoefficientQuotientMap_surjective k V b H)
    change RingHom.ker (Ideal.Quotient.mk H.toIdeal) ≤ p.asHomogeneousIdeal.toIdeal
    rw [Ideal.mk_ker]
    exact hH
  not_irrelevant_le := by
    intro hp
    apply p.not_irrelevant_le
    apply (HomogeneousIdeal.irrelevant_le _).mpr
    intro n hn s hs
    have hq : homogeneousCoefficientQuotientMap k V b H s ∈
        HomogeneousIdeal.irrelevant (quotientCoefficientPiece k V b H) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ hn
        ((homogeneousCoefficientQuotientMap k V b H).map_mem hs)
    have hmem := hp hq
    change s ∈ (p.asHomogeneousIdeal.map (homogeneousCoefficientQuotientMap k V b H)).comap
      (homogeneousCoefficientQuotientMap k V b H) at hmem
    rw [quotient_comap_map k V b H p.asHomogeneousIdeal hH] at hmem
    exact hmem

/-- The lifted actual prime maps to the original actual prime. -/
@[simp] theorem quotientProjectivePointMap_lift
    (p : ProjectiveSpectrum (homogeneousS k V b)) (hH : H ≤ p.asHomogeneousIdeal) :
    quotientProjectivePointMap k V b H (quotientProjectivePointLift k V b H p hH) = p := by
  apply ProjectiveSpectrum.ext
  exact quotient_comap_map k V b H p.asHomogeneousIdeal hH

/-- Actual quotient-point comap is injective by genuine quotient
surjectivity and the native ideal map-comap correspondence. -/
theorem quotientProjectivePointMap_injective :
    Function.Injective (quotientProjectivePointMap k V b H) := by
  intro p q hpq
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk H.toIdeal)
    Ideal.Quotient.mk_surjective
  exact congrArg (fun x : ProjectiveSpectrum (homogeneousS k V b) ↦
    x.asHomogeneousIdeal.toIdeal) hpq

/-- Every actual quotient projective prime lies over the true original
homogeneous ideal, since the genuine quotient kernel lies in every comap. -/
theorem quotientProjectivePointMap_mem_zeroLocus
    (p : ProjectiveSpectrum (quotientCoefficientPiece k V b H)) :
    quotientProjectivePointMap k V b H p ∈
      ProjectiveSpectrum.zeroLocus (homogeneousS k V b) (H : Set (S k V)) := by
  change H.toIdeal ≤ p.asHomogeneousIdeal.toIdeal.comap (Ideal.Quotient.mk H.toIdeal)
  intro s hs
  change Ideal.Quotient.mk H.toIdeal s ∈ p.asHomogeneousIdeal.toIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs]
  exact p.asHomogeneousIdeal.toIdeal.zero_mem

/-- The actual quotient Proj point image is exactly the actual native
zero locus. This is a statement about all relevant homogeneous primes,
not merely ground-field vector lines. -/
theorem quotientProjectivePointMap_range :
    Set.range (quotientProjectivePointMap k V b H) =
      ProjectiveSpectrum.zeroLocus (homogeneousS k V b) (H : Set (S k V)) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact quotientProjectivePointMap_mem_zeroLocus k V b H q
  · intro hp
    exact ⟨quotientProjectivePointLift k V b H p hp,
      quotientProjectivePointMap_lift k V b H p hp⟩

variable [Fintype ι] (K : Submodule k (⋀[k]^2 V))

/-- The genuine canonical resonance scheme's actual native morphism to
the ambient projective coefficient scheme. -/
def actualProjectiveResonanceMap :
    actualProjectiveResonanceScheme k V b K ⟶ AlgebraicGeometry.Proj (homogeneousS k V b) :=
  homogeneousCoefficientProjMap k V b (actualHomogeneousAnnihilator k V b K)

end ChenRanks.Koszul
