import ChenRanks.CharactersSingularFirstCohomology
import ChenRanks.GroupCharacterCup
import ChenRanks.SingularCupCocycleDescent

/-!
# Actual bar cochains on actual singular simplices

The inverse of the actual based transport of an edge has the same
concatenation order as the actual group multiplication. Genuine simplex
edge homotopies prove its triangular multiplication law. The original
inhomogeneous bar cocycle equation then proves native singular closure,
and the original bar differential pulls back to the original singular
differential. No degree-two comparison is a premise.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]

/-- An actual continuous edge, transported to the original based group
and inverted to preserve the original concatenation order. -/
def inverseTransportedContinuousPath (base : X) (p : C(I, X)) :
    FundamentalGroup X base :=
  (ChenRanks.basedFundamentalPath X base (continuousPathAtEndpoints X p))⁻¹

private theorem basedFundamentalPath_ext (base : X)
    {x y x' y' : X} (p : Path x y) (q : Path x' y') (hpq : ∀ t, p t = q t) :
    ChenRanks.basedFundamentalPath X base p =
      ChenRanks.basedFundamentalPath X base q := by
  obtain rfl : x = x' := p.source.symm.trans ((hpq 0).trans q.source)
  obtain rfl : y = y' := p.target.symm.trans ((hpq 1).trans q.target)
  have h : p = q := by ext t; exact hpq t
  rw [h]

theorem inverseTransportedContinuousPath_path (base : X)
    {x y : X} (p : Path x y) :
    inverseTransportedContinuousPath X base p.toContinuousMap =
      (ChenRanks.basedFundamentalPath X base p)⁻¹ := by
  apply congrArg Inv.inv
  exact basedFundamentalPath_ext X base (continuousPathAtEndpoints X p.toContinuousMap)
    p (fun _ => rfl)

/-- Multiplication for the original triangle is proved by its actual
fixed-endpoint edge homotopy and the true native End multiplication. -/
theorem inverseTransportedContinuousPath_triangle (base : X)
    (s : C(stdSimplex ℝ (Fin 3), X)) :
    inverseTransportedContinuousPath X base (s.comp (realTriangleFacePath 1)) =
      inverseTransportedContinuousPath X base (s.comp (realTriangleFacePath 2)) *
        inverseTransportedContinuousPath X base (s.comp (realTriangleFacePath 0)) := by
  change inverseTransportedContinuousPath X base
      (triangleDiagonalEdgePath s).toContinuousMap =
    inverseTransportedContinuousPath X base (triangleFirstEdgePath s).toContinuousMap *
      inverseTransportedContinuousPath X base (triangleSecondEdgePath s).toContinuousMap
  rw [inverseTransportedContinuousPath_path, inverseTransportedContinuousPath_path,
    inverseTransportedContinuousPath_path]
  have hh := ChenRanks.basedFundamentalPath_eq_of_homotopic X base
    (Path.Homotopic.symm ⟨triangleEdgeConcatenationHomotopy s⟩)
  rw [hh, ChenRanks.basedFundamentalPath_trans, mul_inv_rev]

/-- The original group coordinate of the original native singular edge. -/
def inverseTransportedSingularEdge (base : X) (s : simplices X 1) :
    FundamentalGroup X base :=
  inverseTransportedContinuousPath X base (geometricSimplexPath X s)

theorem inverseTransportedSingularEdge_triangle (base : X) (s : simplices X 2) :
    inverseTransportedSingularEdge X base (edge X 1 s) =
      inverseTransportedSingularEdge X base (edge X 2 s) *
        inverseTransportedSingularEdge X base (edge X 0 s) := by
  simp only [inverseTransportedSingularEdge, geometricSimplexPath_edge]
  exact inverseTransportedContinuousPath_triangle X base (geometricSimplex X 2 s)

variable (k : Type) [Field k]

/-- Pull back an actual bar one-cochain on actual original edges. -/
def barOneSingularCochain (base : X) (f : FundamentalGroup X base → k) :
    cochains k X 1 :=
  ofValues k X 1 (fun s => f (inverseTransportedSingularEdge X base s))

/-- Pull back an actual inhomogeneous bar two-cochain on original
ordered consecutive edges. -/
def barTwoSingularCochain (base : X)
    (f : FundamentalGroup X base × FundamentalGroup X base → k) :
    cochains k X 2 :=
  ofValues k X 2 (fun s => f
    (inverseTransportedSingularEdge X base (edge X 2 s),
      inverseTransportedSingularEdge X base (edge X 0 s)))

/-- The actual bar differential pulls back to the actual singular
differential, with both original edge orientations retained. -/
theorem differential_barOneSingularCochain (base : X)
    (f : FundamentalGroup X base → k) :
    differential k X 1 (barOneSingularCochain X k base f) =
      barTwoSingularCochain X k base
        ((groupCohomology.d₁₂
          (ChenRanks.groupTrivialCoefficients k (FundamentalGroup X base))).hom f) := by
  apply cochain_ext k X 2
  intro s
  change values k X 2 (differential k X 1 (barOneSingularCochain X k base f)) s =
    values k X 2 (barTwoSingularCochain X k base
      ((groupCohomology.d₁₂
        (groupTrivialCoefficients k (FundamentalGroup X base))).hom f)) s
  rw [values_differential_one]
  simp only [barOneSingularCochain, barTwoSingularCochain, values_ofValues,
    groupCohomology.d₁₂_hom_apply, Representation.trivial_apply]
  rw [inverseTransportedSingularEdge_triangle]

/-- The true tetrahedral calculation is independent of a presentation
of the actual group. Its input is the actual bar equation, not a
closedness assertion about the resulting singular cochain. -/
private theorem groupCoordinate_barTwo_closed
    (Y G k : Type) [TopologicalSpace Y] [Group G] [Field k]
    (θ : simplices Y 1 → G)
    (hθ : ∀ s : simplices Y 2, θ (edge Y 1 s) = θ (edge Y 2 s) * θ (edge Y 0 s))
    (f : G × G → k)
    (hf : ∀ a b c : G, f (b, c) - f (a * b, c) + f (a, b * c) - f (a, b) = 0) :
    differential k Y 2 (ofValues k Y 2 (fun s => f (θ (edge Y 2 s), θ (edge Y 0 s)))) = 0 := by
  apply cochain_ext k Y 3
  intro s
  change values k Y 3 (differential k Y 2 (ofValues k Y 2 (fun t => f (θ (edge Y 2 t), θ (edge Y 0 t))))) s = 0
  rw [values_differential]
  simp [Fin.sum_univ_succ, values_ofValues, add_assoc]
  norm_num only [pow_succ, pow_zero, neg_mul, mul_neg, one_mul, mul_one, neg_neg]
  simp only [edge]
  let S := TopCat.toSSet.obj (TopCat.of Y)
  have h20 : S.δ (2 : Fin 3) (S.δ (0 : Fin 4) s) =
      S.δ (0 : Fin 3) (S.δ (3 : Fin 4) s) :=
    (S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) s).symm
  have h21 : S.δ (2 : Fin 3) (S.δ (1 : Fin 4) s) =
      S.δ (1 : Fin 3) (S.δ (3 : Fin 4) s) :=
    (S.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) s).symm
  have h22 : S.δ (2 : Fin 3) (S.δ (2 : Fin 4) s) =
      S.δ (2 : Fin 3) (S.δ (3 : Fin 4) s) :=
    (S.δ_comp_δ_apply (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide) s).symm
  have h01 : S.δ (0 : Fin 3) (S.δ (1 : Fin 4) s) =
      S.δ (0 : Fin 3) (S.δ (0 : Fin 4) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide) s
  have h02 : S.δ (0 : Fin 3) (S.δ (2 : Fin 4) s) =
      S.δ (1 : Fin 3) (S.δ (0 : Fin 4) s) :=
    S.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) s
  change f (θ (S.δ 2 (S.δ 0 s)),
        θ (S.δ 0 (S.δ 0 s))) +
      (-f (θ (S.δ 2 (S.δ 1 s)),
        θ (S.δ 0 (S.δ 1 s))) +
      (f (θ (S.δ 2 (S.δ 2 s)),
        θ (S.δ 0 (S.δ 2 s))) +
      -f (θ (S.δ 2 (S.δ 3 s)),
        θ (S.δ 0 (S.δ 3 s))))) = 0
  rw [h20, h21, h22, h01, h02]
  have ht3 := hθ (S.δ 3 s)
  have ht0 := hθ (S.δ 0 s)
  simp only [edge] at ht3 ht0
  change θ (S.δ 1 (S.δ 3 s)) =
    θ (S.δ 2 (S.δ 3 s)) * θ (S.δ 0 (S.δ 3 s)) at ht3
  change θ (S.δ 1 (S.δ 0 s)) =
    θ (S.δ 2 (S.δ 0 s)) * θ (S.δ 0 (S.δ 0 s)) at ht0
  rw [ht3, ht0, h20]
  simpa only [sub_eq_add_neg, add_assoc] using hf
    (θ (S.δ 2 (S.δ 3 s))) (θ (S.δ 0 (S.δ 3 s))) (θ (S.δ 0 (S.δ 0 s)))

/-- Every original bar two-cocycle gives an actual closed singular
two-cochain. The proof uses its actual bar equation and the proved
actual triangular group law, via the true generic tetrahedral calculation. -/
theorem differential_barTwoSingularCochain (base : X)
    (f : groupCohomology.cocycles₂
      (ChenRanks.groupTrivialCoefficients k (FundamentalGroup X base))) :
    differential k X 2 (barTwoSingularCochain X k base f) = 0 := by
  apply groupCoordinate_barTwo_closed X (FundamentalGroup X base) k
    (inverseTransportedSingularEdge X base)
    (inverseTransportedSingularEdge_triangle X base) f
  intro a b c
  have hf := (groupCohomology.mem_cocycles₂_def _).mp f.property a b c
  simpa only [Rep.trivial_ρ_apply] using hf

/-- The actual singular cocycle obtained from a genuine bar cocycle. -/
def barTwoSingularCocycle (base : X)
    (f : groupCohomology.cocycles₂
      (ChenRanks.groupTrivialCoefficients k (FundamentalGroup X base))) :
    cocycles k X 2 :=
  toCocycle k X 2 (barTwoSingularCochain X k base f)
    (differential_barTwoSingularCochain X k base f)

end ChenRanks.SingularCohomology
