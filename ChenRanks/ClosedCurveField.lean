import ChenRanks.ClosedRationalForms
import ChenRanks.DifferentialAlgebraicDependence

/-!
# The actual coefficient field of a finite closed isotropic space

The inputs are a finite-dimensional subspace of the actual rational Kähler
differential module, genuine closedness, and zero genuine exterior products.
The output is an actual intermediate field finite over a rational function
field, together with pullbacks under the original Kähler differential map.
In particular, an ambient-field span does not replace the pullback image.

The geometric realization of this field as a projective curve and resolution
of the resulting rational map are not asserted by this algebraic theorem.
-/

noncomputable section

open scoped BigOperators

namespace ChenRanks

private theorem exteriorWedge_eq_zero_swap {k E : Type*} [Field k]
    [AddCommGroup E] [Module k E] {x y : E}
    (hxy : exteriorWedge (k := k) x y = 0) :
    exteriorWedge (k := k) y x = 0 := by
  have hxy' : ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k y = 0 := by
    simpa only [exteriorWedge_coe] using congrArg Subtype.val hxy
  apply Subtype.ext
  have hswap : ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k y +
      ExteriorAlgebra.ι k y * ExteriorAlgebra.ι k x = 0 :=
    ExteriorAlgebra.ι_add_mul_swap x y
  simpa only [hxy', zero_add, exteriorWedge_coe] using hswap

variable (C : Type*) [Field C] [CharZero C] [IsAlgClosed C]
variable {F : Type*} [Field F] [Algebra C F] [Algebra.EssFiniteType C F]

/-- A finite closed isotropic space of dimension at least two is pulled
back from the actual differential module of a finite extension of `C(h)`.
Neither a curve field nor algebraicity of its coefficients is an input. -/
theorem closed_isotropic_forms_pull_back_from_curve_field
    (P : Submodule C Ω[F⁄C]) [FiniteDimensional C P]
    (hdim : 2 ≤ Module.finrank C P)
    (hclosed : P ≤ closedRationalForms C F)
    (hisotropic : ∀ p q : P,
      exteriorWedge (k := F) (p : Ω[F⁄C]) (q : Ω[F⁄C]) = 0) :
    ∃ (h a : F) (b : Fin (Module.finrank C P) → F),
      Transcendental C h ∧ a ≠ 0 ∧
      FiniteDimensional (IntermediateField.adjoin C {h})
        (curveCoefficientField C h a b) ∧
      ∀ ω : P, ∃ η : Ω[(curveCoefficientField C h a b)⁄C],
        KaehlerDifferential.map C C (curveCoefficientField C h a b) F η =
          (ω : Ω[F⁄C]) := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hdim
  have hli : LinearIndependent C (fun i : Fin 2 ↦ (f i : Ω[F⁄C])) := by
    exact (P.subtype.linearIndependent_iff_of_injOn
      (fun x _ y _ hxy ↦ Subtype.ext hxy)).mpr hf
  let p₁ : Ω[F⁄C] := f 0
  let p₂ : Ω[F⁄C] := f 1
  have hp₁ : p₁ ≠ 0 := hli.ne_zero 0
  have hpair : LinearIndependent C ![p₁, p₂] := by
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨h, hh⟩ := scalar_multiple_of_exteriorWedge_eq_zero hp₁
    (hisotropic (f 0) (f 1))
  have hnotbase : h ∉ Set.range (algebraMap C F) := by
    rintro ⟨c, hc⟩
    have hrel : c • p₁ = (1 : C) • p₂ := by
      rw [one_smul]
      change c • p₁ = (f 1 : Ω[F⁄C])
      rw [hh, ← hc, algebraMap_smul]
    exact one_ne_zero (hpair.eq_zero_of_pair' hrel).2
  have hhtrans : Transcendental C h := transcendental_of_not_mem_base C h hnotbase
  have hdh : KaehlerDifferential.D C F h ≠ 0 :=
    differential_ne_zero_of_transcendental C h hhtrans
  have hp₁closed : IsClosedRationalForm C F p₁ := hclosed (f 0).property
  have hhp₁closed : IsClosedRationalForm C F (h • p₁) := by
    rw [← hh]
    exact hclosed (f 1).property
  obtain ⟨a, ha⟩ := closed_form_eq_smul_differential C F h p₁
    hp₁closed hhp₁closed hdh
  have hane : a ≠ 0 := by
    intro haz
    apply hp₁
    rw [← ha, haz, zero_smul]
  let v := Module.finBasis C P
  have hcoeff : ∀ i, ∃ c : F, (v i : Ω[F⁄C]) = c • p₁ := by
    intro i
    exact scalar_multiple_of_exteriorWedge_eq_zero hp₁
      (hisotropic (f 0) (v i))
  choose b hb using hcoeff
  have haclosed : IsClosedRationalForm C F (a • KaehlerDifferential.D C F h) := by
    rw [ha]
    exact hp₁closed
  have hda : exteriorWedge (k := F) (KaehlerDifferential.D C F h)
      (KaehlerDifferential.D C F a) = 0 :=
    exteriorWedge_eq_zero_swap (closed_smul_differential_wedge_eq_zero C F a h haclosed)
  have hdb : ∀ i, exteriorWedge (k := F) (KaehlerDifferential.D C F h)
      (KaehlerDifferential.D C F (b i)) = 0 := by
    intro i
    have hbclosed : IsClosedRationalForm C F (b i • p₁) := by
      rw [← hb i]
      exact hclosed (v i).property
    have hw := closed_form_wedge_differential_eq_zero C F (b i) p₁
      hp₁closed hbclosed
    rw [← ha] at hw
    have hsmul : a • exteriorWedge (k := F)
        (KaehlerDifferential.D C F (b i)) (KaehlerDifferential.D C F h) = 0 := by
      simpa only [← exteriorWedgeBilin_apply, map_smul] using hw
    exact exteriorWedge_eq_zero_swap ((smul_eq_zero.mp hsmul).resolve_left hane)
  have hfinite := curveCoefficientField_finiteDimensional C h a b hhtrans hda hdb
  refine ⟨h, a, b, hhtrans, hane, hfinite, ?_⟩
  intro ω
  let R := (LinearMap.range
    (KaehlerDifferential.map C C (curveCoefficientField C h a b) F)).restrictScalars C
  have hvmem : ∀ i, (v i : Ω[F⁄C]) ∈ R := by
    intro i
    change (v i : Ω[F⁄C]) ∈ LinearMap.range
      (KaehlerDifferential.map C C (curveCoefficientField C h a b) F)
    rw [hb i, ← ha, smul_smul, mul_comm (b i) a]
    exact curveCoefficientField_form_mem_map_range C h a b i
  have hsum : (∑ i, v.repr ω i • (v i : Ω[F⁄C])) = (ω : Ω[F⁄C]) := by
    simpa only [map_sum, map_smul] using congrArg P.subtype (v.sum_repr ω)
  have hωmem : (ω : Ω[F⁄C]) ∈ R := by
    rw [← hsum]
    exact R.sum_mem fun i _ ↦ R.smul_mem (v.repr ω i) (hvmem i)
  exact hωmem

/-- Actual logarithmic generation supplies closedness for the preceding
curve-field theorem.  No independent closedness assumption remains. -/
theorem logarithmic_isotropic_forms_pull_back_from_curve_field
    (P : Submodule C Ω[F⁄C]) [FiniteDimensional C P]
    (hdim : 2 ≤ Module.finrank C P)
    (hlog : P ≤ Submodule.span C
      (Set.range (logarithmicDifferential C F)))
    (hisotropic : ∀ p q : P,
      exteriorWedge (k := F) (p : Ω[F⁄C]) (q : Ω[F⁄C]) = 0) :
    ∃ (h a : F) (b : Fin (Module.finrank C P) → F),
      Transcendental C h ∧ a ≠ 0 ∧
      FiniteDimensional (IntermediateField.adjoin C {h})
        (curveCoefficientField C h a b) ∧
      ∀ ω : P, ∃ η : Ω[(curveCoefficientField C h a b)⁄C],
        KaehlerDifferential.map C C (curveCoefficientField C h a b) F η =
          (ω : Ω[F⁄C]) := by
  apply closed_isotropic_forms_pull_back_from_curve_field C P hdim ?_ hisotropic
  apply le_trans hlog
  apply Submodule.span_le.mpr
  rintro ω ⟨u, rfl⟩
  exact logarithmicDifferential_isClosed C F u

end ChenRanks
