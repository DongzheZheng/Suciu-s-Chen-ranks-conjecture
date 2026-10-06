import ChenRanks.KoszulPointFreeFibre
import ChenRanks.ResonanceObjects

/-!
# The actual nonzero-point fibre and genuine Aomoto cohomology

The quadratic space is the actual annihilator of the given cup-product
kernel under the genuine exterior determinant pairing. The second
contraction is proved to be the actual dual of exterior multiplication.
The true annihilator image calculation then compares the actual
contraction quotient with genuine Aomoto cohomology, before applying the
proved original tensor-fibre equivalence. No fibre or resonance
comparison is supplied as a hypothesis.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]

/-- The actual vector evaluation functional on the actual dual space. -/
def pointOfVector (e : E) : _root_.Module.Dual k E →ₗ[k] k :=
  _root_.Module.Dual.eval k E e

/-- The true second contraction is the actual dual of exterior
multiplication, transported by the canonical determinant pairing. -/
theorem pointDeltaTwo_pairing (e : E) :
    pointDeltaTwo k (_root_.Module.Dual k E) (pointOfVector k E e) =
      (exteriorWedgeBilin (k := k) e).dualMap.comp (exteriorPower.pairingDual k E 2) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  apply LinearMap.ext
  intro x
  have hf : exteriorPower.ιMulti k 2 f = exteriorWedge (f 0) (f 1) := by
    change exteriorPower.ιMulti k 2 f = exteriorPower.ιMulti k 2 ![f 0, f 1]
    congr 1
    ext i
    fin_cases i <;> rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [hf, pointDeltaTwo_wedge]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    pointOfVector, _root_.Module.Dual.eval_apply, LinearMap.dualMap_apply,
    exteriorWedgeBilin_apply, exteriorWedge, exteriorPower.pairingDual_ιMulti_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul]

/-- The actual kernel of evaluation is the actual annihilator of the
vector's actual one-dimensional span, including its zero-vector degeneration. -/
theorem pointOfVector_ker (e : E) :
    LinearMap.ker (pointOfVector k E e) = (k ∙ e).dualAnnihilator := by
  ext φ
  rw [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
  change φ e = 0 ↔ ∀ x ∈ k ∙ e, φ x = 0
  constructor
  · intro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, h, smul_zero]
  · intro h
    exact h e (Submodule.mem_span_singleton_self e)

/-- Cache the canonical quotient dictionary for the actual evaluation
kernel, without changing its scalar action or quotient relation. -/
local instance pointOfVectorKernel_hasQuotient (e : E) :
    HasQuotient (↥(LinearMap.ker (pointOfVector k E e)))
      (Submodule k (↥(LinearMap.ker (pointOfVector k E e)))) :=
  @Submodule.hasQuotient k (↥(LinearMap.ker (pointOfVector k E e)))
    inferInstance inferInstance inferInstance

variable [FiniteDimensional k E]

/-- A genuine nonzero vector gives a genuine nonzero point of the dual
generator space, by the actual finite basis evaluation injection. -/
theorem pointOfVector_ne_zero {e : E} (he : e ≠ 0) : pointOfVector k E e ≠ 0 := by
  intro h
  apply he
  apply (_root_.Module.finBasis k E).eval_injective
  simpa only [pointOfVector, map_zero] using h

/-- The actual contraction image of the actual quadratic annihilator is
the actual annihilator of the genuine Aomoto cycle space. -/
theorem pointDeltaTwo_exteriorAnnihilator_map
    (I : Submodule k (⋀[k]^2 E)) (e : E) :
    (exteriorAnnihilator k E 2 I).map
        (pointDeltaTwo k (_root_.Module.Dual k E) (pointOfVector k E e)) =
      (ChenRanks.Resonance.aomotoCycles I e).dualAnnihilator := by
  have hp : (exteriorAnnihilator k E 2 I).map (exteriorPower.pairingDual k E 2) =
      I.dualAnnihilator := by
    unfold exteriorAnnihilator
    rw [Submodule.map_comap_eq,
      LinearMap.range_eq_top.mpr (exteriorPairingDual_surjective k E 2), top_inf_eq]
  rw [pointDeltaTwo_pairing, Submodule.map_comp, hp,
    dualAnnihilator_map_dualMap_eq]
  unfold ChenRanks.Resonance.aomotoCycles ChenRanks.Resonance.aomotoDegreeOne
    ChenRanks.Resonance.cupQuotient
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]

/-- The actual quadratic contraction image inside the actual evaluation
kernel is the actual pullback of the Aomoto-cycle annihilator. -/
theorem pointQuadraticRelation_range_comap
    (I : Submodule k (⋀[k]^2 E)) (e : E) :
    LinearMap.range (pointQuadraticRelation k (_root_.Module.Dual k E)
        (exteriorAnnihilator k E 2 I) (pointOfVector k E e)) =
      (ChenRanks.Resonance.aomotoCycles I e).dualAnnihilator.comap
        (LinearMap.ker (pointOfVector k E e)).subtype := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change pointDeltaTwo k (_root_.Module.Dual k E) (pointOfVector k E e)
      (w : ⋀[k]^2 (_root_.Module.Dual k E)) ∈
        (ChenRanks.Resonance.aomotoCycles I e).dualAnnihilator
    rw [← pointDeltaTwo_exteriorAnnihilator_map k E I e]
    exact ⟨w, w.property, rfl⟩
  · intro hz
    change (z : _root_.Module.Dual k E) ∈
      (ChenRanks.Resonance.aomotoCycles I e).dualAnnihilator at hz
    rw [← pointDeltaTwo_exteriorAnnihilator_map k E I e] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    exact ⟨⟨w, hw⟩, Subtype.ext hzw⟩

/-- Nontriviality of the actual contraction quotient is equivalent to
nontriviality of genuine Aomoto cohomology, by the proved annihilator
identification and the true order-reversing annihilator embedding. -/
theorem pointContractionQuotient_nontrivial_iff_aomotoH1
    (I : Submodule k (⋀[k]^2 E)) (e : E) :
    Nontrivial (LinearMap.ker (pointOfVector k E e) ⧸
      LinearMap.range (pointQuadraticRelation k (_root_.Module.Dual k E)
        (exteriorAnnihilator k E 2 I) (pointOfVector k E e))) ↔
      Nontrivial (ChenRanks.Resonance.AomotoH1 I e) := by
  have hLeft : Nontrivial (LinearMap.ker (pointOfVector k E e) ⧸
      LinearMap.range (pointQuadraticRelation k (_root_.Module.Dual k E)
        (exteriorAnnihilator k E 2 I) (pointOfVector k E e))) ↔
      LinearMap.range (pointQuadraticRelation k (_root_.Module.Dual k E)
        (exteriorAnnihilator k E 2 I) (pointOfVector k E e)) ≠ ⊤ :=
    Submodule.Quotient.nontrivial_iff
  rw [hLeft, pointQuadraticRelation_range_comap,
    ne_eq, Submodule.comap_subtype_eq_top, pointOfVector_ker,
    Subspace.dualAnnihilator_le_dualAnnihilator_iff,
    ChenRanks.Resonance.aomotoH1_nontrivial_iff, lt_iff_le_not_ge]
  exact ⟨fun h ↦ ⟨ChenRanks.Resonance.line_le_aomotoCycles I e, h⟩, fun h ↦ h.2⟩

variable [CharZero k]

/-- At a genuine nonzero vector, nontriviality of the literal original
Koszul tensor fibre equals nontriviality of genuine Aomoto cohomology. -/
theorem pointFibre_nontrivial_iff_aomotoH1
    (I : Submodule k (⋀[k]^2 E)) {e : E} (he : e ≠ 0) :
    Nontrivial (PointFiber k (_root_.Module.Dual k E)
      (exteriorAnnihilator k E 2 I) (pointOfVector k E e)) ↔
        Nontrivial (ChenRanks.Resonance.AomotoH1 I e) := by
  rw [(pointFibreContractionEquiv k (_root_.Module.Dual k E)
    (exteriorAnnihilator k E 2 I) (pointOfVector k E e)
    (pointOfVector_ne_zero k E he)).toEquiv.nontrivial_congr]
  exact pointContractionQuotient_nontrivial_iff_aomotoH1 k E I e

/-- The actual nonzero-point tensor fibre detects the actual resonance
point set. No affine origin or projective scheme equality is asserted. -/
theorem pointFibre_nontrivial_iff_resonance
    (I : Submodule k (⋀[k]^2 E)) {e : E} (he : e ≠ 0) :
    Nontrivial (PointFiber k (_root_.Module.Dual k E)
      (exteriorAnnihilator k E 2 I) (pointOfVector k E e)) ↔
        e ∈ ChenRanks.Resonance.resonance I := by
  rw [pointFibre_nontrivial_iff_aomotoH1 k E I he,
    ChenRanks.Resonance.mem_resonance_iff_aomotoH1_nontrivial I he]

end ChenRanks.Koszul
