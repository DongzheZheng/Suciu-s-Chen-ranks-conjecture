import ChenRanks.KoszulSeparationQuadraticLifts
import ChenRanks.KoszulLocalizedTransverse
import ChenRanks.KoszulPointAomoto

/-!
# Separation eliminates localized transverse classes

Exterior separation gives the quadratic lifts used by the local
Nakayama argument. In the localization of the Koszul module, these lifts
eliminate transverse exterior classes and show that transverse
coordinates annihilate the pivot exterior classes.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

private theorem transverseCoordinate_kills_pivotClass_of_mixed_zero
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R]
    (v w u : V)
    (hwu : coefficientExtendedExteriorClass k V K R (exteriorWedge w u) = 0)
    (hvu : coefficientExtendedExteriorClass k V K R (exteriorWedge v u) = 0) :
    extendedCoefficient k V R u •
      coefficientExtendedExteriorClass k V K R (exteriorWedge v w) = 0 := by
  have ht := coefficientExtendedExteriorClass_third k V K R v w u
  simpa only [hwu, hvu, smul_zero, sub_zero, zero_add] using ht

variable {τ : Type*} (U : Submodule k V) (b : _root_.Module.Basis τ k U)

/-- The actual embedded basis spans the original subspace. -/
theorem subtypeBasis_span : Submodule.span k (Set.range fun i ↦ (b i : V)) = U := by
  have h : (Submodule.span k (Set.range b)).map U.subtype = U := by
    rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def] using h

/-- Every actual pure exterior correction has its constant tensor in
the genuine polynomial-linear span of pure basis wedges. The statement
is proved by two actual span arguments for the actual bilinear wedge. -/
theorem pureExterior_constantTensor_mem_pureTransverseSpan
    {h : ⋀[k]^2 V} (hh : h ∈ pureExterior U) :
    (1 : S k V) ⊗ₜ[k] h ∈ pureTransverseSecondSpan k V (fun i ↦ (b i : V)) := by
  let N := pureTransverseSecondSpan k V (fun i ↦ (b i : V))
  let B : V →ₗ[k] V →ₗ[k] C2 k V :=
    exteriorWedgeBilin.compr₂ (TensorProduct.mk k (S k V) (⋀[k]^2 V) 1)
  have hinner (i : τ) : U ≤ (N.restrictScalars k).comap (B (b i : V)) := by
    apply le_trans (le_of_eq (subtypeBasis_span k V U b).symm)
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  have houter (q : U) : U ≤ (N.restrictScalars k).comap (B.flip (q : V)) := by
    apply le_trans (le_of_eq (subtypeBasis_span k V U b).symm)
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact hinner i q.property
  have hpure : pureExterior U ≤ (N.restrictScalars k).comap
      (TensorProduct.mk k (S k V) (⋀[k]^2 V) 1) := by
    rw [pureExterior_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨p, q, rfl⟩
    exact houter q p.property
  exact hpure hh

private theorem pureCorrection_zero_of_transverseSpan_zero
    (K : Submodule k (⋀[k]^2 V)) (R : Type*) [CommRing R] [Algebra (S k V) R]
    [IsLocalRing R] (v : V)
    (hv : IsUnit (extendedCoefficient k V R v))
    (hu : ∀ i, extendedCoefficient k V R (b i : V) ∈ IsLocalRing.maximalIdeal R)
    (hN : extendedTransverseSpan k V K R (fun i ↦ (b i : V)) v = ⊥)
    {h : ⋀[k]^2 V} (hh : h ∈ pureExterior U) :
    coefficientExtendedExteriorClass k V K R h = 0 := by
  have hmem := pureTransverseSecondSpan_image_mem_maximal_smul k V K R
    (fun i ↦ (b i : V)) v hv hu
    (pureExterior_constantTensor_mem_pureTransverseSpan k V U b hh)
  rw [hN, Submodule.smul_bot] at hmem
  exact (Submodule.mem_bot R).mp hmem

variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (P : Submodule k E) (I : Submodule k (⋀[k]^2 E))

omit [AddCommGroup V] [_root_.Module k V] in
/-- True separation provides exactly the actual quadratic tensor lifts
required by local Nakayama. No tensor-lift condition is an input. -/
theorem actual_separation_quadratic_tensor_lifts
    (c : _root_.Module.Basis τ k P.dualAnnihilator)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P)
    (v : _root_.Module.Dual k E) (i : τ) :
    ∃ h : C2 k (_root_.Module.Dual k E),
      h ∈ pureTransverseSecondSpan k (_root_.Module.Dual k E) (fun i ↦ (c i : _root_.Module.Dual k E)) ∧
        (1 : S k (_root_.Module.Dual k E)) ⊗ₜ[k] exteriorWedge v (c i : _root_.Module.Dual k E) + h ∈
          LinearMap.range (quadraticInclusion k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) := by
  obtain ⟨h, hh, hK⟩ := exists_corrected_mixed_quadratic_relation k E P I hsep v (c i)
  refine ⟨(1 : S k (_root_.Module.Dual k E)) ⊗ₜ[k] h,
    pureExterior_constantTensor_mem_pureTransverseSpan k (_root_.Module.Dual k E)
      P.dualAnnihilator c hh, ?_⟩
  refine ⟨(1 : S k (_root_.Module.Dual k E)) ⊗ₜ[k]
    (⟨exteriorWedge v (c i : _root_.Module.Dual k E) + h, hK⟩ : exteriorAnnihilator k E 2 I), ?_⟩
  rw [quadraticInclusion_tmul, TensorProduct.tmul_add]

variable [Fintype τ]

omit [AddCommGroup V] [_root_.Module k V] in
/-- In the actual localization at a true point in `P`, separation itself
eliminates the true transverse span. Both the actual quadratic tensor
lifts and the actual maximal-ideal coordinate conditions are proved. -/
theorem actualPointLocalized_transverseSpan_eq_bot_of_separation
    (c : _root_.Module.Basis τ k P.dualAnnihilator)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P)
    (e : E) (heP : e ∈ P) (v : _root_.Module.Dual k E) (hv : v e = 1) :
    extendedTransverseSpan k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
        (fun i ↦ (c i : _root_.Module.Dual k E)) v = ⊥ := by
  apply actualPointLocalized_transverseSpan_eq_bot k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I) (fun i ↦ (c i : _root_.Module.Dual k E)) v
    (pointOfVector k E e)
  · exact hv
  · intro i
    exact (Submodule.mem_dualAnnihilator _).mp (c i).property e heP
  · exact actual_separation_quadratic_tensor_lifts k E P I c hsep v

omit [AddCommGroup V] [_root_.Module k V] in
/-- Every true pure transverse correction vanishes in the literal
localized original module, by the proved actual basis span and Nakayama. -/
theorem actualPointLocalized_pureCorrection_eq_zero_of_separation
    (c : _root_.Module.Basis τ k P.dualAnnihilator)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P)
    (e : E) (heP : e ∈ P) (v : _root_.Module.Dual k E) (hv : v e = 1)
    {h : ⋀[k]^2 (_root_.Module.Dual k E)} (hh : h ∈ pureExterior P.dualAnnihilator) :
    coefficientExtendedExteriorClass k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)) h = 0 := by
  exact pureCorrection_zero_of_transverseSpan_zero k (_root_.Module.Dual k E)
    P.dualAnnihilator c (exteriorAnnihilator k E 2 I)
    (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)) v
    (pointLocalCoefficient_isUnit k (_root_.Module.Dual k E) (pointOfVector k E e) hv)
    (fun i ↦ pointLocalCoefficient_mem_maximal k (_root_.Module.Dual k E)
      (pointOfVector k E e) ((Submodule.mem_dualAnnihilator _).mp (c i).property e heP))
    (actualPointLocalized_transverseSpan_eq_bot_of_separation k E P I c hsep e heP v hv) hh

omit [AddCommGroup V] [_root_.Module k V] in
/-- Separation eliminates every actual mixed transverse exterior class,
including classes with an arbitrary first dual factor. -/
theorem actualPointLocalized_mixedClass_eq_zero_of_separation
    (c : _root_.Module.Basis τ k P.dualAnnihilator)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P)
    (e : E) (heP : e ∈ P) (v : _root_.Module.Dual k E) (hv : v e = 1)
    (w : _root_.Module.Dual k E) (u : P.dualAnnihilator) :
    coefficientExtendedExteriorClass k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
        (exteriorWedge w (u : _root_.Module.Dual k E)) = 0 := by
  let R := PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)
  obtain ⟨h, hh, hK⟩ := exists_corrected_mixed_quadratic_relation k E P I hsep w u
  have hrel : (1 : S k (_root_.Module.Dual k E)) ⊗ₜ[k]
      (exteriorWedge w (u : _root_.Module.Dual k E) + h) ∈
        LinearMap.range (quadraticInclusion k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)) :=
    ⟨(1 : S k (_root_.Module.Dual k E)) ⊗ₜ[k]
      (⟨exteriorWedge w (u : _root_.Module.Dual k E) + h, hK⟩ : exteriorAnnihilator k E 2 I), rfl⟩
  have hzero := coefficientExtendedSecondMap_quadratic k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I) R _ hrel
  rw [TensorProduct.tmul_add, map_add] at hzero
  change coefficientExtendedExteriorClass k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I) R
      (exteriorWedge w (u : _root_.Module.Dual k E)) +
    coefficientExtendedExteriorClass k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I) R h = 0 at hzero
  rw [actualPointLocalized_pureCorrection_eq_zero_of_separation k E P I c hsep e heP v hv hh,
    add_zero] at hzero
  exact hzero

omit [AddCommGroup V] [_root_.Module k V] in
/-- The actual transverse coordinate annihilates every actual pivot
class, by the original third relation and proved mixed-class vanishing. -/
theorem actualPointLocalized_transverseCoordinate_kills_pivotClass
    (c : _root_.Module.Basis τ k P.dualAnnihilator)
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P)
    (e : E) (heP : e ∈ P) (v : _root_.Module.Dual k E) (hv : v e = 1)
    (w : _root_.Module.Dual k E) (u : P.dualAnnihilator) :
    extendedCoefficient k (_root_.Module.Dual k E)
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
        (u : _root_.Module.Dual k E) •
      coefficientExtendedExteriorClass k (_root_.Module.Dual k E) (exteriorAnnihilator k E 2 I)
        (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e))
          (exteriorWedge v w) = 0 := by
  exact transverseCoordinate_kills_pivotClass_of_mixed_zero k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I)
      (PointLocalCoefficientRing k (_root_.Module.Dual k E) (pointOfVector k E e)) v w u
    (actualPointLocalized_mixedClass_eq_zero_of_separation k E P I c hsep e heP v hv w u)
    (actualPointLocalized_mixedClass_eq_zero_of_separation k E P I c hsep e heP v hv v u)

end ChenRanks.Koszul
