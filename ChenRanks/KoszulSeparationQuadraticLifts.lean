import ChenRanks.KoszulComponentDuality
import ChenRanks.KoszulThirdObjects
import Mathlib.Algebra.Module.Projective

/-!
# Actual exterior separation produces genuine corrected mixed relations

The mixed exterior space is proved to be the kernel of the true exterior
square of the quotient map. Naturality of the actual determinant pairing
then identifies its actual annihilator with the exterior square of the
ordinary annihilator subspace. Thus separation yields actual quadratic
relations with corrections in that actual transverse exterior square.

No block-pairing identity, mixed-projection surjectivity, quadratic lift,
localized vanishing, or annihilator radicality is supplied as a premise.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]

private theorem exteriorMap_wedge
    {F : Type*} [AddCommGroup F] [_root_.Module k F]
    (f : E →ₗ[k] F) (x y : E) :
    exteriorPower.map 2 f (exteriorWedge x y) = exteriorWedge (f x) (f y) := by
  simp only [exteriorWedge, exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The actual mixed exterior square is the kernel of the true quotient
exterior map. A genuine linear section of the quotient is derived over
the field, rather than introduced as a kernel-decomposition premise. -/
theorem mixedExterior_eq_ker_quotientExterior (P : Submodule k E) :
    mixedExterior P = LinearMap.ker (exteriorPower.map 2 P.mkQ) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨p, x, rfl⟩
    change exteriorPower.map 2 P.mkQ (exteriorWedge (p : E) x) = 0
    rw [exteriorMap_wedge]
    have hp : P.mkQ (p : E) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr p.property
    rw [hp]
    change exteriorWedgeBilin (0 : E ⧸ P) (P.mkQ x) = 0
    rw [map_zero, LinearMap.zero_apply]
  · obtain ⟨s, hs⟩ := P.mkQ.exists_rightInverse_of_surjective P.range_mkQ
    have hs_apply (x : E ⧸ P) : P.mkQ (s x) = x := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using DFunLike.congr_fun hs x
    have hP (x : E) : x - s (P.mkQ x) ∈ P := by
      apply (Submodule.Quotient.mk_eq_zero P).mp
      change P.mkQ (x - s (P.mkQ x)) = 0
      rw [map_sub, hs_apply, sub_self]
    let d : (⋀[k]^2 E) →ₗ[k] (⋀[k]^2 E) :=
      LinearMap.id - exteriorPower.map 2 (s.comp P.mkQ)
    have hspan : (⊤ : Submodule k (⋀[k]^2 E)) ≤ (mixedExterior P).comap d := by
      rw [← exteriorWedge_span (k := k) (E := E)]
      apply Submodule.span_le.mpr
      rintro z ⟨x, y, rfl⟩
      change exteriorWedge x y -
        exteriorPower.map 2 (s.comp P.mkQ) (exteriorWedge x y) ∈ mixedExterior P
      rw [exteriorMap_wedge]
      have heq : exteriorWedge (k := k) x y - exteriorWedge (s (P.mkQ x)) (s (P.mkQ y)) =
          exteriorWedge (x - s (P.mkQ x)) y +
            exteriorWedge (s (P.mkQ x)) (y - s (P.mkQ y)) := by
        simp only [← exteriorWedgeBilin_apply, map_sub, LinearMap.sub_apply]
        abel
      change exteriorWedge x y - exteriorWedge (s (P.mkQ x)) (s (P.mkQ y)) ∈ _
      rw [heq]
      apply (mixedExterior P).add_mem
      · exact exteriorWedge_mem_mixed P ⟨x - s (P.mkQ x), hP x⟩ y
      · rw [wedgeTwo_swap]
        exact (mixedExterior P).neg_mem
          (exteriorWedge_mem_mixed P ⟨y - s (P.mkQ y), hP y⟩ (s (P.mkQ x)))
    intro z hz
    have hz' : exteriorPower.map 2 P.mkQ z = 0 := hz
    have hmap : exteriorPower.map 2 (s.comp P.mkQ) z = 0 := by
      rw [exteriorPower.map_comp, LinearMap.comp_apply, hz', map_zero]
    have hmem := hspan (show z ∈ (⊤ : Submodule k (⋀[k]^2 E)) from trivial)
    change z - exteriorPower.map 2 (s.comp P.mkQ) z ∈ mixedExterior P at hmem
    simpa only [hmap, sub_zero] using hmem

/-- Exterior square commutes with the actual range of a linear map. The
surjectivity onto that true range is derived from the actual range map. -/
theorem range_exteriorMap_eq_pureExterior_range
    {F : Type*} [AddCommGroup F] [_root_.Module k F] (f : E →ₗ[k] F) :
    LinearMap.range (exteriorPower.map 2 f) = pureExterior (LinearMap.range f) := by
  have hcomp : (LinearMap.range f).subtype.comp f.rangeRestrict = f := by
    ext x
    rfl
  have hmap : exteriorPower.map 2 f =
      (exteriorPower.map 2 (LinearMap.range f).subtype).comp
        (exteriorPower.map 2 f.rangeRestrict) := by
    rw [← exteriorPower.map_comp, hcomp]
  have hs : LinearMap.range (exteriorPower.map 2 f.rangeRestrict) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (exteriorPower.map_surjective (LinearMap.range_eq_top.mp f.range_rangeRestrict))
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ hs]
  rfl

variable [FiniteDimensional k E]

/-- The true mixed-space annihilator is exactly the actual exterior
square of the ordinary annihilator subspace. The identity follows from
the true quotient exterior kernel and determinant-pairing naturality. -/
theorem exteriorAnnihilator_mixedExterior (P : Submodule k E) :
    exteriorAnnihilator k E 2 (mixedExterior P) = pureExterior P.dualAnnihilator := by
  have hU : LinearMap.range P.mkQ.dualMap = P.dualAnnihilator := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, P.ker_mkQ]
  have hH : LinearMap.range (exteriorPower.map 2 P.mkQ.dualMap) =
      pureExterior P.dualAnnihilator := by
    rw [range_exteriorMap_eq_pureExterior_range k (_root_.Module.Dual k (E ⧸ P)), hU]
  have hdual : LinearMap.range (exteriorPower.map 2 P.mkQ).dualMap =
      (mixedExterior P).dualAnnihilator := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      ← mixedExterior_eq_ker_quotientExterior]
  ext z
  constructor
  · intro hz
    have hz' : exteriorPower.pairingDual k E 2 z ∈
        LinearMap.range (exteriorPower.map 2 P.mkQ).dualMap := by
      rw [hdual]
      exact hz
    obtain ⟨φ, hφ⟩ := hz'
    obtain ⟨w, hw⟩ := exteriorPairingDual_surjective k (E ⧸ P) 2 φ
    have hn := DFunLike.congr_fun
      (exteriorPairingDual_naturality k (E ⧸ P) E P.mkQ 2) w
    change exteriorPower.pairingDual k E 2 (exteriorPower.map 2 P.mkQ.dualMap w) =
      (exteriorPower.map 2 P.mkQ).dualMap (exteriorPower.pairingDual k (E ⧸ P) 2 w) at hn
    have heq : exteriorPower.map 2 P.mkQ.dualMap w = z :=
      (exteriorPairingDual_bijective k E 2).1 (hn.trans (by rw [hw]; exact hφ))
    rw [← hH]
    exact ⟨w, heq⟩
  · intro hz
    rw [← hH] at hz
    obtain ⟨w, rfl⟩ := hz
    have hn := DFunLike.congr_fun
      (exteriorPairingDual_naturality k (E ⧸ P) E P.mkQ 2) w
    change exteriorPower.pairingDual k E 2 (exteriorPower.map 2 P.mkQ.dualMap w) =
      (exteriorPower.map 2 P.mkQ).dualMap (exteriorPower.pairingDual k (E ⧸ P) 2 w) at hn
    change exteriorPower.pairingDual k E 2 (exteriorPower.map 2 P.mkQ.dualMap w) ∈
      (mixedExterior P).dualAnnihilator
    rw [hn, ← hdual]
    exact LinearMap.mem_range_self _ _

/-- Ordinary intersection-annihilator duality is transported through
the proved bijective actual exterior pairing. -/
theorem exteriorAnnihilator_inf (n : ℕ) (I J : Submodule k (⋀[k]^n E)) :
    exteriorAnnihilator k E n (I ⊓ J) =
      exteriorAnnihilator k E n I ⊔ exteriorAnnihilator k E n J := by
  unfold exteriorAnnihilator
  rw [Subspace.dualAnnihilator_inf_eq]
  apply Submodule.comap_sup_of_injective (exteriorPairingDual_bijective k E n).1
  · rw [LinearMap.range_eq_top.mpr (exteriorPairingDual_surjective k E n)]
    exact le_top
  · rw [LinearMap.range_eq_top.mpr (exteriorPairingDual_surjective k E n)]
    exact le_top

omit [FiniteDimensional k E] in
/-- A genuine mixed dual wedge annihilates the actual exterior square
of `P`, directly by the actual two-by-two determinant pairing. -/
theorem mixedDualWedge_mem_pureExterior_annihilator (P : Submodule k E)
    (v : _root_.Module.Dual k E) (u : P.dualAnnihilator) :
    exteriorWedge v (u : _root_.Module.Dual k E) ∈
      exteriorAnnihilator k E 2 (pureExterior P) := by
  have hker : pureExterior P ≤ LinearMap.ker
      (exteriorPower.pairingDual k E 2 (exteriorWedge v (u : _root_.Module.Dual k E))) := by
    rw [pureExterior_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨p, q, rfl⟩
    have hp : (u : _root_.Module.Dual k E) (p : E) = 0 :=
      (Submodule.mem_dualAnnihilator _).mp u.property (p : E) p.property
    have hq : (u : _root_.Module.Dual k E) (q : E) = 0 :=
      (Submodule.mem_dualAnnihilator _).mp u.property (q : E) q.property
    change exteriorPower.pairingDual k E 2 (exteriorWedge v (u : _root_.Module.Dual k E))
      (exteriorWedge (p : E) (q : E)) = 0
    simp only [exteriorWedge, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hp, hq, mul_zero, zero_mul, sub_self]
  change exteriorPower.pairingDual k E 2 (exteriorWedge v (u : _root_.Module.Dual k E)) ∈
    (pureExterior P).dualAnnihilator
  exact (Submodule.mem_dualAnnihilator _).mpr (fun z hz ↦ hker hz)

/-- Actual exterior separation produces a genuine quadratic relation
whose correction belongs to the actual pure transverse exterior square.
No mixed-projection or quadratic-lift condition is an input. -/
theorem exists_corrected_mixed_quadratic_relation
    (P : Submodule k E) (I : Submodule k (⋀[k]^2 E))
    (hsep : I ⊓ mixedExterior P ≤ pureExterior P)
    (v : _root_.Module.Dual k E) (u : P.dualAnnihilator) :
    ∃ h : ⋀[k]^2 (_root_.Module.Dual k E), h ∈ pureExterior P.dualAnnihilator ∧
      exteriorWedge v (u : _root_.Module.Dual k E) + h ∈ exteriorAnnihilator k E 2 I := by
  have hm := mixedDualWedge_mem_pureExterior_annihilator k E P v u
  have hm' : exteriorWedge v (u : _root_.Module.Dual k E) ∈
      exteriorAnnihilator k E 2 (I ⊓ mixedExterior P) :=
    Submodule.dualAnnihilator_anti hsep hm
  rw [exteriorAnnihilator_inf, exteriorAnnihilator_mixedExterior] at hm'
  obtain ⟨x, hx, h, hh, heq⟩ := Submodule.mem_sup.mp hm'
  refine ⟨-h, (pureExterior P.dualAnnihilator).neg_mem hh, ?_⟩
  have heq' : exteriorWedge v (u : _root_.Module.Dual k E) + -h = x := by
    rw [← heq]
    exact add_neg_cancel_right x h
  rw [heq']
  exact hx

end ChenRanks.Koszul
