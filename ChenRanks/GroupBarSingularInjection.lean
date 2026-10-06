import ChenRanks.GroupBarSingularCochains
import ChenRanks.SingularSquareCocycleHomotopy
import ChenRanks.SingularPathConcatenationTriangle

/-!
# Genuine degree-two injection on native bar cocycle representatives

An arbitrary actual bar cocycle is normalized by an actual bar boundary.
If its actual singular pullback has an actual primitive, the primitive's
values on based loops are invariant under genuine fixed-endpoint
homotopy: both square triangles have a constant edge, on which the
normalized bar cocycle is zero. These values therefore descend through
the original fundamental-group quotient. Original path-concatenation
triangles give an actual bar primitive. The native H² vanishing criteria
then prove the equivalence of vanishing of the two actual classes.

No classifying map, Hopf sequence, H² injection, or loop-invariance
detector is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace ChenRanks

variable (k G : Type) [Field k] [Group G]

/-- An actual bar boundary that removes the constant degeneracy value. -/
def barConstantBoundary (c : k) : groupCohomology.cocycles₂ (groupTrivialCoefficients k G) :=
  ⟨(groupCohomology.d₁₂ (groupTrivialCoefficients k G)).hom (fun _ => c),
    groupCohomology.d₁₂_apply_mem_cocycles₂
      (A := groupTrivialCoefficients k G) (fun _ : G => c)⟩

@[simp]
theorem barConstantBoundary_apply (c : k) (g h : G) :
    barConstantBoundary k G c (g, h) = c := by
  change ((groupCohomology.d₁₂ (groupTrivialCoefficients k G)).hom
    (fun _ => c)) (g, h) = c
  simp only [groupCohomology.d₁₂_hom_apply, Representation.trivial_apply,
    sub_self, zero_add]

theorem barConstantBoundary_class (c : k) :
    groupCohomology.H2π (groupTrivialCoefficients k G) (barConstantBoundary k G c) = 0 := by
  apply (groupCohomology.H2π_eq_zero_iff _).mpr
  exact ⟨(fun _ => c), rfl⟩

/-- Normalization is subtraction of an actual boundary in the original
native cocycle module. -/
def normalizedBarCocycle (f : groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k G) :=
  f - barConstantBoundary k G (f (1, 1))

@[simp]
theorem normalizedBarCocycle_apply
    (f : groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) (g h : G) :
    normalizedBarCocycle k G f (g, h) = f (g, h) - f (1, 1) := by
  change f (g, h) - barConstantBoundary k G (f (1, 1)) (g, h) = _
  rw [barConstantBoundary_apply]

@[simp]
theorem normalizedBarCocycle_one_left
    (f : groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) (g : G) :
    normalizedBarCocycle k G f (1, g) = 0 := by
  rw [normalizedBarCocycle_apply, groupCohomology.cocycles₂_map_one_fst, sub_self]

@[simp]
theorem normalizedBarCocycle_one_right
    (f : groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) (g : G) :
    normalizedBarCocycle k G f (g, 1) = 0 := by
  rw [normalizedBarCocycle_apply, groupCohomology.cocycles₂_map_one_snd]
  simp only [Representation.trivial_apply, sub_self]

/-- The actual normalized cocycle has exactly the original native H² class. -/
theorem normalizedBarCocycle_class
    (f : groupCohomology.cocycles₂ (groupTrivialCoefficients k G)) :
    groupCohomology.H2π (groupTrivialCoefficients k G) (normalizedBarCocycle k G f) =
      groupCohomology.H2π (groupTrivialCoefficients k G) f := by
  rw [normalizedBarCocycle, map_sub, barConstantBoundary_class, sub_zero]

end ChenRanks

namespace ChenRanks.SingularCohomology

variable (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
variable (k : Type) [Field k]

private theorem inverseTransportedSingularEdge_refl (base x : X) :
    inverseTransportedSingularEdge X base (simplexOfPath X (Path.refl x).toContinuousMap) = 1 := by
  simp only [inverseTransportedSingularEdge, geometricSimplexPath_simplexOfPath,
    inverseTransportedContinuousPath_path, basedFundamentalPath_refl, inv_one]

/-- Primitive values are truly invariant under actual based homotopy.
The vanishing on constant edges is the actual normalization equation. -/
theorem normalizedBarPrimitive_based_homotopy (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base)))
    (hl : ∀ g, f (1, g) = 0) (hr : ∀ g, f (g, 1) = 0)
    (β : cochains k X 1) (hβ : differential k X 1 β = barTwoSingularCochain X k base f)
    {p q : Path base base} (H : p.Homotopy q) :
    actualPathCochainValue k X β p = actualPathCochainValue k X β q := by
  let F : C(I × I, X) :=
    ⟨fun z => H (z.2, z.1), H.continuous.comp continuous_swap⟩
  have hv : ∀ t : I, F (1, t) = F (0, t) := by
    intro t
    change H (t, 1) = H (t, 0)
    rw [Path.Homotopy.target, Path.Homotopy.source]
  have hcP : edge X 0 (squarePositiveSimplex X F) =
      simplexOfPath X (Path.refl base).toContinuousMap := by
    apply geometricSimplexPath_injective
    ext t
    rw [geometricSimplexPath_edge, geometricSimplexPath_simplexOfPath]
    change geometricSimplex X 2 (squarePositiveSimplex X F)
        (realTriangleFacePath 0 t) = base
    rw [geometricSimplex_squarePositiveSimplex, realSquarePositiveTriangle_face]
    exact H.target t
  have hcN : edge X 2 (squareNegativeSimplex X F) =
      simplexOfPath X (Path.refl base).toContinuousMap := by
    rw [← square_vertical_edges_eq X F hv, hcP]
  have hp := values_differential_one k X β (squarePositiveSimplex X F)
  have hn := values_differential_one k X β (squareNegativeSimplex X F)
  rw [hβ] at hp hn
  simp only [barTwoSingularCochain, values_ofValues, hcP, hcN,
    inverseTransportedSingularEdge_refl, hl, hr] at hp hn
  rw [square_diagonal_edges_eq X F] at hp
  have hb : squareBottomPath X F = p.toContinuousMap := by
    ext t
    exact H.toHomotopy.apply_zero t
  have ht : squareTopPath X F = q.toContinuousMap := by
    ext t
    exact H.toHomotopy.apply_one t
  unfold actualPathCochainValue
  rw [← hb, ← ht, simplexOfPath_squareBottomPath, simplexOfPath_squareTopPath]
  linear_combination hn - hp

/-- Actual primitive evaluation descends through the original quotient
of based paths, not through a synthetic loop equivalence. -/
def normalizedBarPrimitiveLoopValue (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base)))
    (hl : ∀ g, f (1, g) = 0) (hr : ∀ g, f (g, 1) = 0)
    (β : cochains k X 1) (hβ : differential k X 1 β = barTwoSingularCochain X k base f)
    (g : FundamentalGroup X base) : k :=
  Quotient.lift (fun p : Path base base => actualPathCochainValue k X β p)
    (by
      intro p q hpq
      obtain ⟨H⟩ := hpq
      exact normalizedBarPrimitive_based_homotopy X k base f hl hr β hβ H)
    g.toPath

@[simp]
theorem normalizedBarPrimitiveLoopValue_mk (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base)))
    (hl : ∀ g, f (1, g) = 0) (hr : ∀ g, f (g, 1) = 0)
    (β : cochains k X 1) (hβ : differential k X 1 β = barTwoSingularCochain X k base f)
    (p : Path base base) :
    normalizedBarPrimitiveLoopValue X k base f hl hr β hβ
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      actualPathCochainValue k X β p := rfl

/-- The original concatenation triangle gives the actual primitive
identity; the native group's reverse multiplication order is explicit. -/
theorem normalizedBarPrimitiveLoopValue_mul (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base)))
    (hl : ∀ g, f (1, g) = 0) (hr : ∀ g, f (g, 1) = 0)
    (β : cochains k X 1) (hβ : differential k X 1 β = barTwoSingularCochain X k base f)
    (g h : FundamentalGroup X base) :
    normalizedBarPrimitiveLoopValue X k base f hl hr β hβ (g * h) =
      normalizedBarPrimitiveLoopValue X k base f hl hr β hβ g +
        normalizedBarPrimitiveLoopValue X k base f hl hr β hβ h - f (h⁻¹, g⁻¹) := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction h using Path.Homotopic.Quotient.ind with
    | mk q =>
      have ht := values_differential_one k X β (pathConcatenationTriangle X q p)
      rw [hβ] at ht
      have h0 : edge X 0 (pathConcatenationTriangle X q p) =
          simplexOfPath X p.toContinuousMap := by
        simp [edge_pathConcatenationTriangle]
      have h1 : edge X 1 (pathConcatenationTriangle X q p) =
          simplexOfPath X (q.trans p).toContinuousMap := by
        simp [edge_pathConcatenationTriangle]
      have h2 : edge X 2 (pathConcatenationTriangle X q p) =
          simplexOfPath X q.toContinuousMap := by
        simp [edge_pathConcatenationTriangle]
      simp only [barTwoSingularCochain, values_ofValues] at ht
      rw [h0, h1, h2] at ht
      simp only [inverseTransportedSingularEdge, geometricSimplexPath_simplexOfPath,
        inverseTransportedContinuousPath_path, basedFundamentalPath_loop] at ht
      change actualPathCochainValue k X β (q.trans p) =
        actualPathCochainValue k X β p + actualPathCochainValue k X β q -
          f ((FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q))⁻¹,
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))⁻¹)
      unfold actualPathCochainValue
      linear_combination ht

/-- Every actual singular primitive of the normalized bar pullback
produces a genuine primitive in the original inhomogeneous bar complex. -/
theorem normalizedBarCocycle_class_zero_of_singular_primitive (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base)))
    (hl : ∀ g, f (1, g) = 0) (hr : ∀ g, f (g, 1) = 0)
    (β : cochains k X 1) (hβ : differential k X 1 β = barTwoSingularCochain X k base f) :
    groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base)) f = 0 := by
  apply (groupCohomology.H2π_eq_zero_iff _).mpr
  refine ⟨fun g => normalizedBarPrimitiveLoopValue X k base f hl hr β hβ g⁻¹, ?_⟩
  funext gh
  simp only [groupCohomology.d₁₂_hom_apply, Representation.trivial_apply]
  have hm := normalizedBarPrimitiveLoopValue_mul X k base f hl hr β hβ gh.2⁻¹ gh.1⁻¹
  simp only [inv_inv, ← mul_inv_rev] at hm
  linear_combination -hm

/-- Normalization on the bar side is an actual singular boundary after
pullback, so a given primitive is adjusted by that actual one-cochain. -/
theorem normalizedBar_singular_primitive (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base)))
    (β : cochains k X 1) (hβ : differential k X 1 β = barTwoSingularCochain X k base f) :
    differential k X 1 (β - barOneSingularCochain X k base (fun _ => f (1, 1))) =
      barTwoSingularCochain X k base
        (normalizedBarCocycle k (FundamentalGroup X base) f) := by
  rw [map_sub, hβ, differential_barOneSingularCochain]
  apply cochain_ext k X 2
  intro s
  change values k X 2 (barTwoSingularCochain X k base f -
      barTwoSingularCochain X k base
        ((groupCohomology.d₁₂
          (groupTrivialCoefficients k (FundamentalGroup X base))).hom
            (fun _ => f (1, 1)))) s =
    values k X 2 (barTwoSingularCochain X k base
      (normalizedBarCocycle k (FundamentalGroup X base) f)) s
  simp only [map_sub, Pi.sub_apply, barTwoSingularCochain, values_ofValues,
    normalizedBarCocycle_apply, groupCohomology.d₁₂_hom_apply,
    Representation.trivial_apply, sub_self, zero_add]

/-- On the genuine native bar cocycle representatives, vanishing of
the actual singular pullback class is equivalent to vanishing of the
actual native group H² class. No injection is a premise. -/
theorem barTwoSingularCocycle_class_zero_iff (base : X)
    (f : groupCohomology.cocycles₂
      (groupTrivialCoefficients k (FundamentalGroup X base))) :
    cocycleClass k X 2 (barTwoSingularCocycle X k base f) = 0 ↔
      groupCohomology.H2π (groupTrivialCoefficients k (FundamentalGroup X base)) f = 0 := by
  constructor
  · intro hs
    obtain ⟨β, hβ⟩ := (mem_positive_boundaries_iff k X 1 _).mp
      ((cocycleClass_eq_zero_iff k X 2 _).mp hs)
    change differential k X 1 β = barTwoSingularCochain X k base f at hβ
    rw [← normalizedBarCocycle_class k (FundamentalGroup X base) f]
    exact normalizedBarCocycle_class_zero_of_singular_primitive X k base _
      (normalizedBarCocycle_one_left k (FundamentalGroup X base) f)
      (normalizedBarCocycle_one_right k (FundamentalGroup X base) f)
      (β - barOneSingularCochain X k base (fun _ => f (1, 1)))
      (normalizedBar_singular_primitive X k base f β hβ)
  · intro hg
    obtain ⟨a, ha⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hg
    apply (cocycleClass_eq_zero_iff k X 2 _).mpr
    apply (mem_positive_boundaries_iff k X 1 _).mpr
    refine ⟨barOneSingularCochain X k base a, ?_⟩
    rw [differential_barOneSingularCochain, ha]
    rfl

end ChenRanks.SingularCohomology
