import ChenRanks.DifferentialFieldTransport
import ChenRanks.CurveDifferentialLine

/-!
# The actual one-dimensional curve differential mechanism after field transport

An actual field comparison transports the already constructed curve
basis. Tensor induction proves that the entire actual base-change image
is a single line in the actual model function field, hence is isotropic.
No isotropy of the actual image is supplied as a hypothesis.
-/

noncomputable section

namespace ChenRanks

open scoped TensorProduct

variable {k L K G : Type*} [Field k] [CharZero k]
  [Field L] [Field K] [Field G] [Algebra k L] [Algebra k K]
  [Algebra k G] [Algebra K G] [IsScalarTower k K G]

/-- The actual field isomorphism transports a proved generating curve one-form. -/
theorem curve_differentials_eq_smul_of_actual_field_equiv
    (e : L ≃ₐ[k] K) (v : Ω[L⁄k])
    (hv : ∀ ω : Ω[L⁄k], ∃ a : L, a • v = ω) (η : Ω[K⁄k]) :
    ∃ a : K, a • differentialFieldLinearEquiv e v = η := by
  obtain ⟨ω, hω⟩ := (differentialFieldLinearEquiv e).surjective η
  obtain ⟨a, ha⟩ := hv ω
  refine ⟨e a, ?_⟩
  rw [← differentialFieldLinearEquiv_smul, ha, hω]

/-- Every actual base-change tensor maps into the transported actual line. -/
theorem actual_curve_baseChange_eq_smul_of_field_equiv
    (e : L ≃ₐ[k] K) (v : Ω[L⁄k])
    (hv : ∀ ω : Ω[L⁄k], ∃ a : L, a • v = ω)
    (t : G ⊗[K] Ω[K⁄k]) :
    ∃ a : G, a • KaehlerDifferential.map k k K G (differentialFieldLinearEquiv e v) =
      KaehlerDifferential.mapBaseChange k K G t := by
  induction t with
  | zero => exact ⟨0, by simp only [zero_smul, map_zero]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [add_smul, ha, hb, map_add]⟩
  | tmul a η =>
    obtain ⟨b, hb⟩ := curve_differentials_eq_smul_of_actual_field_equiv e v hv η
    refine ⟨a * algebraMap K G b, ?_⟩
    rw [← hb, KaehlerDifferential.mapBaseChange_tmul,
      (KaehlerDifferential.map k k K G).map_smul,
      ← IsScalarTower.algebraMap_smul G b, smul_smul]

/-- The actual transported image has no nonzero exterior products. -/
theorem actual_curve_baseChange_exteriorWedge_eq_zero_of_field_equiv
    (e : L ≃ₐ[k] K) (v : Ω[L⁄k])
    (hv : ∀ ω : Ω[L⁄k], ∃ a : L, a • v = ω)
    (α β : Ω[G⁄k])
    (hα : α ∈ LinearMap.range (KaehlerDifferential.mapBaseChange k K G))
    (hβ : β ∈ LinearMap.range (KaehlerDifferential.mapBaseChange k K G)) :
    exteriorWedge (k := G) α β = 0 := by
  obtain ⟨x, hx⟩ := hα
  obtain ⟨y, hy⟩ := hβ
  obtain ⟨a, ha⟩ := actual_curve_baseChange_eq_smul_of_field_equiv e v hv x
  obtain ⟨b, hb⟩ := actual_curve_baseChange_eq_smul_of_field_equiv e v hv y
  rw [← hx, ← hy, ← ha, ← hb]
  apply Subtype.ext
  simp [exteriorWedge_coe]

section ActualFiniteCurve

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [FiniteDimensional (RatFunc k) L]

/-- For the actual finite rational-function extension, the original
basis condition is proved, and actual image isotropy is unconditional. -/
theorem finite_curve_baseChange_exteriorWedge_eq_zero_of_actual_field_equiv
    (e : L ≃ₐ[k] K) (α β : Ω[G⁄k])
    (hα : α ∈ LinearMap.range (KaehlerDifferential.mapBaseChange k K G))
    (hβ : β ∈ LinearMap.range (KaehlerDifferential.mapBaseChange k K G)) :
    exteriorWedge (k := G) α β = 0 := by
  letI : Algebra.IsSeparable (RatFunc k) L := inferInstance
  exact actual_curve_baseChange_exteriorWedge_eq_zero_of_field_equiv e
    (curveDifferentialGenerator k L) (curve_differential_eq_smul k L) α β hα hβ

end ActualFiniteCurve

end ChenRanks
