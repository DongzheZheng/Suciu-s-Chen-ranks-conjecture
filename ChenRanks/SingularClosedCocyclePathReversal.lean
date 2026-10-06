import ChenRanks.SingularPartialTriangleBoundary

/-!
# Native reversal identities for actual closed one-cochains

The constant actual two-simplex first proves zero on constant paths.
The actual triangle q ↦ γ(q₁) then has the original reverse, constant,
and forward paths as its genuine faces. Its native singular closure
relation proves the signed reversal identity for every actual path.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

def actualIntervalReversal : C(I, I) where
  toFun t := ⟨1 - (t : ℝ), sub_nonneg.mpr t.property.2, by linarith [t.property.1]⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk
    (fun t : I => ⟨sub_nonneg.mpr t.property.2, by linarith [t.property.1]⟩)

def actualReversedContinuousPath {X : Type} [TopologicalSpace X] (γ : C(I, X)) : C(I, X) :=
  γ.comp actualIntervalReversal

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

theorem closedOne_constant_path_value_eq_zero
    (β : cochains k X 1) (hβ : differential k X 1 β = 0) (x : X) :
    values k X 1 β (simplexOfPath X (ContinuousMap.const I x)) = 0 := by
  let F : C(stdSimplex ℝ (Fin 3), X) := ContinuousMap.const _ x
  have hface (i : Fin 3) : F.comp (realTriangleFacePath i) = ContinuousMap.const I x := by
    apply ContinuousMap.ext
    intro t
    rfl
  have h := closedOne_triangle_relation k X β hβ (simplexOfActualTriangle F)
  simp only [edge_simplexOfActualTriangle, hface] at h
  linear_combination -h

def actualPathReversalTriangleMap (γ : C(I, X)) : C(stdSimplex ℝ (Fin 3), X) :=
  γ.comp ⟨fun q => (⟨q 1, q.property.1 1, stdSimplex.le_one q 1⟩ : I),
    ((continuous_apply 1).comp continuous_subtype_val).subtype_mk
      (fun q : stdSimplex ℝ (Fin 3) => ⟨q.property.1 1, stdSimplex.le_one q 1⟩)⟩

theorem actualPathReversalTriangleMap_face (γ : C(I, X)) (i : Fin 3) :
    (actualPathReversalTriangleMap X γ).comp (realTriangleFacePath i) =
      if i = 0 then actualReversedContinuousPath γ
      else if i = 1 then ContinuousMap.const I (γ 0) else γ := by
  fin_cases i <;> apply ContinuousMap.ext <;> intro t
  · apply congrArg γ
    apply Subtype.ext
    change realTriangleFacePath 0 t 1 = 1 - (t : ℝ)
    simp [realTriangleFacePath_coordinate, Fin.succAbove]
  · change γ (⟨realTriangleFacePath 1 t 1,
      (realTriangleFacePath 1 t).property.1 1,
      stdSimplex.le_one (realTriangleFacePath 1 t) 1⟩ : I) = γ 0
    apply congrArg γ
    apply Subtype.ext
    change realTriangleFacePath 1 t 1 = 0
    simp [realTriangleFacePath_coordinate, Fin.succAbove]
  · apply congrArg γ
    apply Subtype.ext
    change realTriangleFacePath 2 t 1 = (t : ℝ)
    simp [realTriangleFacePath_coordinate, Fin.succAbove]

/-- Signed reversal is derived for every genuine path from the native
closed-cochain relation, with no path-generation premise. -/
theorem closedOne_reversed_path_value
    (β : cochains k X 1) (hβ : differential k X 1 β = 0) (γ : C(I, X)) :
    values k X 1 β (simplexOfPath X (actualReversedContinuousPath γ)) =
      -values k X 1 β (simplexOfPath X γ) := by
  have h := closedOne_triangle_relation k X β hβ
    (simplexOfActualTriangle (actualPathReversalTriangleMap X γ))
  simp only [edge_simplexOfActualTriangle, actualPathReversalTriangleMap_face,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_true, ite_false,
    closedOne_constant_path_value_eq_zero k X β hβ] at h
  linear_combination -h

end ChenRanks.SingularCohomology
