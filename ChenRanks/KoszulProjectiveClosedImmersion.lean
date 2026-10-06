import ChenRanks.KoszulProjectiveQuotientMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The genuine projective quotient is a native closed immersion

The topology is derived from native zero loci and actual quotient
surjectivity. Surjectivity of the actual homogeneous-localization maps
is derived by lifting the genuine homogeneous numerator and denominator
of each genuine fraction through the actual quotient degree images.
The native Proj stalk isomorphisms then identify those maps with the
actual scheme stalk maps. No stalk-surjectivity or closed-immersion
property is supplied as a hypothesis.
-/

noncomputable section

open CategoryTheory Topology

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable {ι : Type*} (b : _root_.Module.Basis ι k V)
variable (H : HomogeneousIdeal (homogeneousS k V b))

/-- Native projective zero-locus preimages follow the actual ring map. -/
theorem quotientProjectivePointMap_preimage_zeroLocus (T : Set (S k V)) :
    quotientProjectivePointMap k V b H ⁻¹'
        ProjectiveSpectrum.zeroLocus (homogeneousS k V b) T =
      ProjectiveSpectrum.zeroLocus (quotientCoefficientPiece k V b H)
        (homogeneousCoefficientQuotientMap k V b H '' T) := by
  ext p
  change T ⊆ homogeneousCoefficientQuotientMap k V b H ⁻¹'
      (p.asHomogeneousIdeal : Set (HomogeneousCoefficientQuotient k V b H)) ↔
    homogeneousCoefficientQuotientMap k V b H '' T ⊆ p.asHomogeneousIdeal
  exact Set.image_subset_iff.symm

/-- The actual quotient-point map induces the true native Proj topology. -/
theorem quotientProjectivePointMap_isInducing :
    IsInducing (quotientProjectivePointMap k V b H) where
  eq_induced := by
    simp only [TopologicalSpace.ext_iff, ← isClosed_compl_iff,
      ProjectiveSpectrum.isClosed_iff_zeroLocus, isClosed_induced_iff]
    refine fun Z ↦ ⟨?_, ?_⟩
    · rintro ⟨F, hF⟩
      refine ⟨ProjectiveSpectrum.zeroLocus (homogeneousS k V b)
        (homogeneousCoefficientQuotientMap k V b H ⁻¹' F),
        ⟨homogeneousCoefficientQuotientMap k V b H ⁻¹' F, rfl⟩, ?_⟩
      rw [quotientProjectivePointMap_preimage_zeroLocus,
        Function.Surjective.image_preimage (homogeneousCoefficientQuotientMap_surjective k V b H),
        hF]
    · rintro ⟨_, ⟨F, rfl⟩, hF⟩
      exact ⟨homogeneousCoefficientQuotientMap k V b H '' F,
        hF.symm.trans (quotientProjectivePointMap_preimage_zeroLocus k V b H F)⟩

/-- The actual map is a native closed topological embedding on every
relevant homogeneous prime, without a ground-field-points restriction. -/
theorem quotientProjectivePointMap_isClosedEmbedding :
    IsClosedEmbedding (quotientProjectivePointMap k V b H) where
  toIsInducing := quotientProjectivePointMap_isInducing k V b H
  injective := quotientProjectivePointMap_injective k V b H
  isClosed_range := by
    rw [quotientProjectivePointMap_range]
    exact ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- The actual homogeneous local ring map is surjective because both
the numerator and denominator of each actual homogeneous fraction have
actual lifts in the matching original homogeneous degree. -/
theorem quotient_homogeneousLocalRingHom_surjective
    (p : ProjectiveSpectrum (quotientCoefficientPiece k V b H)) :
    Function.Surjective
      (HomogeneousLocalization.localRingHom
        (homogeneousCoefficientQuotientMap k V b H)
        (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal
        p.asHomogeneousIdeal.toIdeal rfl) := by
  intro z
  obtain ⟨c, rfl⟩ := z.mk_surjective
  obtain ⟨num, hnum, enum⟩ := c.num.property
  obtain ⟨den, hden, eden⟩ := c.den.property
  have hd : den ∈ (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal.primeCompl := by
    change homogeneousCoefficientQuotientMap k V b H den ∉ p.asHomogeneousIdeal.toIdeal
    change Ideal.Quotient.mk H.toIdeal den = (c.den : HomogeneousCoefficientQuotient k V b H) at eden
    rw [homogeneousCoefficientQuotientMap_apply, eden]
    exact c.den_mem
  let d : HomogeneousLocalization.NumDenSameDeg (homogeneousS k V b)
      (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨c.deg, ⟨num, hnum⟩, ⟨den, hden⟩, hd⟩
  refine ⟨HomogeneousLocalization.mk d, ?_⟩
  rw [HomogeneousLocalization.localRingHom, HomogeneousLocalization.map_mk]
  apply congrArg HomogeneousLocalization.mk
  refine HomogeneousLocalization.NumDenSameDeg.ext _ (c2 := c) ?_ ?_ ?_
  · rfl
  · exact enum
  · exact eden

/-- The native actual projective quotient morphism is surjective on
actual stalks, using the native true Proj stalk isomorphisms. -/
instance homogeneousCoefficientProjMap_surjectiveOnStalks :
    AlgebraicGeometry.SurjectiveOnStalks (homogeneousCoefficientProjMap k V b H) where
  stalkMap_surjective p := by
    letI : CommRing (HomogeneousLocalization.AtPrime (quotientCoefficientPiece k V b H)
        p.asHomogeneousIdeal.toIdeal) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
        (𝒜 := quotientCoefficientPiece k V b H) (x := p.asHomogeneousIdeal.toIdeal.primeCompl)
    letI : CommRing (HomogeneousLocalization.AtPrime (homogeneousS k V b)
        (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
        (𝒜 := homogeneousS k V b)
        (x := (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal.primeCompl)
    have hlocal := quotient_homogeneousLocalRingHom_surjective k V b H p
    have hleft := (ConcreteCategory.bijective_of_isIso
      (AlgebraicGeometry.Proj.stalkIso (homogeneousS k V b)
        (quotientProjectivePointMap k V b H p)).hom).2
    have hright := (ConcreteCategory.bijective_of_isIso
      (AlgebraicGeometry.Proj.stalkIso (quotientCoefficientPiece k V b H) p).inv).2
    have hcomp := hright.comp (hlocal.comp hleft)
    change Function.Surjective
      ((AlgebraicGeometry.Proj.stalkIso (homogeneousS k V b)
          (quotientProjectivePointMap k V b H p)).hom ≫
        CommRingCat.ofHom (HomogeneousLocalization.localRingHom
          (homogeneousCoefficientQuotientMap k V b H)
          (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal
          p.asHomogeneousIdeal.toIdeal rfl) ≫
        (AlgebraicGeometry.Proj.stalkIso (quotientCoefficientPiece k V b H) p).inv) at hcomp
    have hstalk :
        (AlgebraicGeometry.Proj.stalkIso (homogeneousS k V b)
            (quotientProjectivePointMap k V b H p)).hom ≫
          CommRingCat.ofHom (HomogeneousLocalization.localRingHom
            (homogeneousCoefficientQuotientMap k V b H)
            (quotientProjectivePointMap k V b H p).asHomogeneousIdeal.toIdeal
            p.asHomogeneousIdeal.toIdeal rfl) ≫
          (AlgebraicGeometry.Proj.stalkIso (quotientCoefficientPiece k V b H) p).inv =
        (homogeneousCoefficientProjMap k V b H).stalkMap p :=
      AlgebraicGeometry.Proj.localRingHom_comp_stalkIso
        (homogeneousCoefficientQuotientMap k V b H) (quotient_irrelevant_le_map k V b H) p
    rw [hstalk] at hcomp
    exact hcomp

/-- The true quotient Proj morphism is a native closed immersion. -/
instance homogeneousCoefficientProjMap_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion (homogeneousCoefficientProjMap k V b H) where
  isClosedEmbedding := quotientProjectivePointMap_isClosedEmbedding k V b H

variable [Fintype ι] (K : Submodule k (⋀[k]^2 V))

/-- The canonical original-module resonance scheme is a genuine native
closed subscheme of the actual ambient projective coefficient scheme. -/
instance actualProjectiveResonanceMap_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion (actualProjectiveResonanceMap k V b K) :=
  homogeneousCoefficientProjMap_isClosedImmersion k V b (actualHomogeneousAnnihilator k V b K)

end ChenRanks.Koszul
