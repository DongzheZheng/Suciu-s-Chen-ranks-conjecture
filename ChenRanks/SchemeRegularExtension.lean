import ChenRanks.NoCodimensionOnePoles

/-!
# Actual scheme sections from absence of codimension-one poles

The ambient function field is the actual stalk at the generic point of an
integral scheme.  The affine coordinate rings are actual structure-sheaf
sections.  Their fraction-field instances are proved by mathlib, not
postulated.  Local sections are constructed by the normal-domain theorem,
shown compatible using their actual germs, and glued by the actual sheaf.

Integral closedness of the affine section rings is an explicit structural
input.  This file does not derive that input from smoothness, and it does
not construct the manuscript's horizontal/vertical divisor geometry.
-/

namespace ChenRanks

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

variable (X : Scheme.{u}) [IsIntegral X]

private theorem genericPoint_mem_nonempty_open (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The actual affine prime localization, represented inside the actual
scheme function field by the proved affine fraction-field comparison. -/
def affinePrimeLocalizationInFunctionField (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (p : Ideal Γ(X, U)) (hp : p.IsPrime) :
    Subalgebra Γ(X, U) X.functionField := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact primeLocalizationInFractionField Γ(X, U) X.functionField p hp

/-- Actual restriction does not change the actual generic-point germ. -/
theorem germToFunctionField_restrict
    (U V : X.Opens) [Nonempty U] [Nonempty V] (hUV : U ≤ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map (homOfLE hUV).op s) =
      X.germToFunctionField V s := by
  exact X.presheaf.germ_res_apply (homOfLE hUV) (genericPoint X)
    (genericPoint_mem_nonempty_open X U) s

/-- Actual absence of height-one poles on an actual normal affine chart
constructs a unique actual regular section with the prescribed rational
germ.  The actual coordinate ring and function field are not identified
by an additional hypothesis. -/
theorem existsUnique_affine_section_of_no_codimension_one_poles
    [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (x : X.functionField)
    (hx : ∀ p : Ideal Γ(X, U), ∀ hp : p.IsPrime, p.height = 1 →
      x ∈ affinePrimeLocalizationInFunctionField X U hU p hp) :
    ∃! s : Γ(X, U), X.germToFunctionField U s = x := by
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨s, hs⟩ := regular_of_no_codimension_one_poles Γ(X, U) X.functionField x hx
  change X.germToFunctionField U s = x at hs
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact X.germToFunctionField_injective U (ht.trans hs.symm)

/-- Actual affine regular representatives of a single actual rational
function agree on overlaps and glue to a unique actual structure-sheaf
section.  Each representative is derived from height-one local membership;
compatibility and gluing are proved, not assumed. -/
theorem existsUnique_section_of_affine_no_codimension_one_poles
    [IsLocallyNoetherian X] (V : X.Opens) [Nonempty V]
    {ι : Type u} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hAffine : ∀ i, IsAffineOpen (U i)) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ iSup U) (hNormal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    (x : X.functionField)
    (hx : ∀ i, ∀ p : Ideal Γ(X, U i), ∀ hp : p.IsPrime, p.height = 1 →
      x ∈ affinePrimeLocalizationInFunctionField X (U i) (hAffine i) p hp) :
    ∃! s : Γ(X, V), X.germToFunctionField V s = x := by
  classical
  have hlocal : ∀ i, ∃ s : Γ(X, U i), X.germToFunctionField (U i) s = x := by
    intro i
    letI : IsIntegrallyClosed Γ(X, U i) := hNormal i
    obtain ⟨s, hs, _⟩ := existsUnique_affine_section_of_no_codimension_one_poles
      X (U i) (hAffine i) x (hx i)
    exact ⟨s, hs⟩
  choose sf hsf using hlocal
  have hCompat : TopCat.Presheaf.IsCompatible X.presheaf U sf := by
    intro i j
    haveI hOverlap : Nonempty (↑(U i ⊓ U j) : Set X) :=
      ⟨⟨genericPoint X, genericPoint_mem_nonempty_open X (U i),
        genericPoint_mem_nonempty_open X (U j)⟩⟩
    change X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (sf i) =
      X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (sf j)
    apply @AlgebraicGeometry.Scheme.germToFunctionField_injective X inferInstance
      (U i ⊓ U j) hOverlap
    rw [@germToFunctionField_restrict X inferInstance (U i ⊓ U j) (U i)
        hOverlap inferInstance inf_le_left (sf i),
      @germToFunctionField_restrict X inferInstance (U i ⊓ U j) (U j)
        hOverlap inferInstance inf_le_right (sf j),
      hsf i, hsf j]
  obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' U V
    (fun i ↦ homOfLE (hUV i)) hcover sf hCompat
  obtain ⟨i, _⟩ := Opens.mem_iSup.mp
    (hcover (genericPoint_mem_nonempty_open X V))
  have hsgerm : X.germToFunctionField V s = x := by
    calc
      X.germToFunctionField V s =
          X.germToFunctionField (U i) (X.presheaf.map (homOfLE (hUV i)).op s) :=
        (germToFunctionField_restrict X (U i) V (hUV i) s).symm
      _ = X.germToFunctionField (U i) (sf i) := congrArg _ (hs i)
      _ = x := hsf i
  refine ⟨s, hsgerm, ?_⟩
  intro t ht
  exact X.germToFunctionField_injective V (ht.trans hsgerm.symm)

end

end ChenRanks
