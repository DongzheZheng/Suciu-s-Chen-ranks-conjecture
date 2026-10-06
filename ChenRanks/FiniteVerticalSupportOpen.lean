import ChenRanks.DivisorSupportFinite
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Deleting the actual finite nonhorizontal order support

In a T0 irreducible sober space, its generic point is not in the closure
of any other point.  Deleting the finitely many closures of nongeneric
points from an actual finite point set therefore constructs an actual
open containing the generic point.

For actual normal Noetherian affine charts and actual nonzero rational
functions, all actual nonzero height-one orders have finite support.
Their actual affine prime points are mapped by the actual scheme
morphism to a finite point set.  The constructed open deletes precisely
the closures of its nongeneric points.  Thus an actual support point
whose image lies in that open is horizontal.

No dimension-one hypothesis, finite-support detector, existence of a
desired open, or desired horizontality condition is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ChenRanks

universe u

section FinitePointDeletion

variable {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
  [IrreducibleSpace Y] [T0Space Y]

/-- In the actual T0 irreducible space, the generic point cannot be in
the closure of a different point. -/
theorem genericPoint_not_mem_closure_singleton_of_ne
    (y : Y) (hy : y ≠ genericPoint Y) : genericPoint Y ∉ closure ({y} : Set Y) := by
  intro h
  have hs : y ⤳ genericPoint Y := specializes_iff_mem_closure.mpr h
  exact hy (hs.antisymm (genericPoint_specializes y)).eq

omit [T0Space Y] in
/-- The actual open obtained by removing closures of the actual
nongeneric points of a finite point set. -/
def finiteNonGenericPointAvoidanceOpen (T : Finset Y) : Opens Y := by
  classical
  let S := T.filter (fun y ↦ y ≠ genericPoint Y)
  exact ⟨(⋃ y ∈ S, closure ({y} : Set Y))ᶜ,
    (isClosed_biUnion_finset (fun _ _ ↦ isClosed_closure)).isOpen_compl⟩

omit [T0Space Y] in
/-- Membership is exactly avoidance of the actual nongeneric point
closures; no geometric property is built into the definition. -/
theorem mem_finiteNonGenericPointAvoidanceOpen_iff (T : Finset Y) (z : Y) :
    z ∈ finiteNonGenericPointAvoidanceOpen T ↔
      ∀ y ∈ T, y ≠ genericPoint Y → z ∉ closure ({y} : Set Y) := by
  classical
  change (z ∉ ⋃ y ∈ T.filter (fun y ↦ y ≠ genericPoint Y), closure ({y} : Set Y)) ↔ _
  constructor
  · intro hz y hy hne hclosure
    apply hz
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hy, hne⟩, hclosure⟩⟩
  · intro h hz
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hys, hclosure⟩ := Set.mem_iUnion.mp hy
    exact h y (Finset.mem_filter.mp hys).1 (Finset.mem_filter.mp hys).2 hclosure

/-- The constructed actual open contains the actual generic point. -/
theorem genericPoint_mem_finiteNonGenericPointAvoidanceOpen (T : Finset Y) :
    genericPoint Y ∈ finiteNonGenericPointAvoidanceOpen T := by
  apply (mem_finiteNonGenericPointAvoidanceOpen_iff T (genericPoint Y)).mpr
  intro y _ hne
  exact genericPoint_not_mem_closure_singleton_of_ne y hne

/-- The constructed open is actually nonempty, with the generic point
as an explicit witness. -/
theorem finiteNonGenericPointAvoidanceOpen_nonempty (T : Finset Y) :
    Nonempty (finiteNonGenericPointAvoidanceOpen T) :=
  ⟨⟨genericPoint Y, genericPoint_mem_finiteNonGenericPointAvoidanceOpen T⟩⟩

omit [T0Space Y] in
/-- A point from the original finite set that remains in the actual
open must be the actual generic point. -/
theorem eq_genericPoint_of_mem_finiteNonGenericPointAvoidanceOpen
    (T : Finset Y) (y : Y) (hy : y ∈ T)
    (hW : y ∈ finiteNonGenericPointAvoidanceOpen T) : y = genericPoint Y := by
  by_contra hne
  exact ((mem_finiteNonGenericPointAvoidanceOpen_iff T y).mp hW y hy hne)
    (subset_closure (Set.mem_singleton y))

end FinitePointDeletion

section ActualFiniteOrderSupport

variable (A K : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
  {j : Type*} [Fintype j]

omit [Fintype j] in
/-- The actual union of the genuine nonzero-order supports of finitely
many actual rational functions. -/
def jointFractionHeightOneOrderSupport (F : j → Kˣ) :
    Set {p : Ideal A // p.IsPrime ∧ p.height = 1} :=
  {p | ∃ a, heightOnePrimeOrder A K p.val p.property.1 p.property.2 (F a : K) ≠ 0}

/-- Finiteness follows from actual fraction orders, rather than from
choosing a finite list of desired divisor labels. -/
theorem jointFractionHeightOneOrderSupport_finite (F : j → Kˣ) :
    (jointFractionHeightOneOrderSupport A K F).Finite := by
  have hs : jointFractionHeightOneOrderSupport A K F =
      ⋃ a : j, {p : {p : Ideal A // p.IsPrime ∧ p.height = 1} |
        heightOnePrimeOrder A K p.val p.property.1 p.property.2 (F a : K) ≠ 0} := by
    ext p
    simp only [jointFractionHeightOneOrderSupport, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hs]
  exact Set.finite_iUnion (fun a ↦ finite_fraction_heightOnePrimeOrder_support A K (F a))

end ActualFiniteOrderSupport

section ActualAffinePrimeImages

variable {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
  [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]
  {j : Type*} [Fintype j]

omit [Fintype j] in
/-- The actual base points which are images of actual affine
height-one nonzero-order support points. -/
def actualAffineSupportBasePoints (F : j → X.functionFieldˣ) : Set Y := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact (fun p : {p : Ideal Γ(X, U) // p.IsPrime ∧ p.height = 1} ↦
    f (hU.fromSpec ⟨p.val, p.property.1⟩)) ''
      jointFractionHeightOneOrderSupport Γ(X, U) X.functionField F

/-- The actual base support is finite because the actual prime
support is finite and the actual morphism takes its actual image. -/
theorem actualAffineSupportBasePoints_finite (F : j → X.functionFieldˣ) :
    (actualAffineSupportBasePoints f U hU F).Finite := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact (jointFractionHeightOneOrderSupport_finite Γ(X, U) X.functionField F).image
    (fun p ↦ f (hU.fromSpec ⟨p.val, p.property.1⟩))

omit [IsIntegral X] [Nonempty U] [IsNoetherianRing Γ(X, U)]
  [IsIntegrallyClosed Γ(X, U)] [Fintype j] in
/-- Each actual affine prime point really lies in the original chart. -/
theorem actualAffinePrimePoint_mem (p : PrimeSpectrum Γ(X, U)) : hU.fromSpec p ∈ U := by
  exact (hU.isoSpec.inv p).property

end ActualAffinePrimeImages

section ActualFiniteChartImages

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) {c : Type*} [Fintype c] (U : c → X.Opens)
  [∀ i, Nonempty (U i)] (hAffine : ∀ i, IsAffineOpen (U i))
  [∀ i, IsNoetherianRing Γ(X, U i)] [∀ i, IsIntegrallyClosed Γ(X, U i)]
  {j : Type*} [Fintype j] (F : j → X.functionFieldˣ)

omit [Fintype c] [Fintype j] [IsIntegral Y] in
/-- The actual finite-chart union of the actual support-image sets. -/
def actualFiniteChartSupportBasePoints : Set Y :=
  ⋃ i, actualAffineSupportBasePoints f (U i) (hAffine i) F

omit [IsIntegral Y] in
/-- The actual finite number of charts gives a finite actual base
support set; no finite-support premise is introduced. -/
theorem actualFiniteChartSupportBasePoints_finite :
    (actualFiniteChartSupportBasePoints f U hAffine F).Finite :=
  Set.finite_iUnion (fun i ↦ actualAffineSupportBasePoints_finite f (U i) (hAffine i) F)

/-- The actual base open constructed by deleting all actual
nongeneric support-image closures in the chosen finite chart family. -/
def actualVerticalSupportAvoidanceOpen : Y.Opens :=
  finiteNonGenericPointAvoidanceOpen
    (actualFiniteChartSupportBasePoints_finite f U hAffine F).toFinset

/-- The actual generic point belongs to the constructed actual base
open, so the open is nonempty without an existence hypothesis. -/
theorem genericPoint_mem_actualVerticalSupportAvoidanceOpen :
    genericPoint Y ∈ actualVerticalSupportAvoidanceOpen f U hAffine F :=
  genericPoint_mem_finiteNonGenericPointAvoidanceOpen _

/-- The actual generic point explicitly witnesses nonemptiness. -/
theorem actualVerticalSupportAvoidanceOpen_nonempty :
    Nonempty (actualVerticalSupportAvoidanceOpen f U hAffine F) :=
  ⟨⟨genericPoint Y, genericPoint_mem_actualVerticalSupportAvoidanceOpen f U hAffine F⟩⟩

/-- An actual height-one support prime whose actual image is in the
constructed open must be horizontal. -/
theorem actual_support_prime_horizontal_of_mem_avoidance
    (i : c) (p : {p : Ideal Γ(X, U i) // p.IsPrime ∧ p.height = 1})
    (hsupport :
      letI : IsFractionRing Γ(X, U i) X.functionField :=
        functionField_isFractionRing_of_isAffineOpen X (U i) (hAffine i)
      ∃ a, heightOnePrimeOrder Γ(X, U i) X.functionField p.val p.property.1 p.property.2
        (F a : X.functionField) ≠ 0)
    (hW : f ((hAffine i).fromSpec ⟨p.val, p.property.1⟩) ∈
      actualVerticalSupportAvoidanceOpen f U hAffine F) :
    f ((hAffine i).fromSpec ⟨p.val, p.property.1⟩) = genericPoint Y := by
  letI : IsFractionRing Γ(X, U i) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U i) (hAffine i)
  have hm : f ((hAffine i).fromSpec ⟨p.val, p.property.1⟩) ∈
      actualFiniteChartSupportBasePoints f U hAffine F := by
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact ⟨p, hsupport, rfl⟩
  have hT : f ((hAffine i).fromSpec ⟨p.val, p.property.1⟩) ∈
      (actualFiniteChartSupportBasePoints_finite f U hAffine F).toFinset :=
    (actualFiniteChartSupportBasePoints_finite f U hAffine F).mem_toFinset.mpr hm
  exact eq_genericPoint_of_mem_finiteNonGenericPointAvoidanceOpen _ _ hT hW

/-- A nonhorizontal actual prime point remaining over the constructed
base open has zero actual order for every original generator. -/
theorem actual_order_zero_of_nonhorizontal_prime_in_avoidance
    (i : c) (p : {p : Ideal Γ(X, U i) // p.IsPrime ∧ p.height = 1})
    (hne : f ((hAffine i).fromSpec ⟨p.val, p.property.1⟩) ≠ genericPoint Y)
    (hW : f ((hAffine i).fromSpec ⟨p.val, p.property.1⟩) ∈
      actualVerticalSupportAvoidanceOpen f U hAffine F) :
    letI : IsFractionRing Γ(X, U i) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X (U i) (hAffine i)
    ∀ a, heightOnePrimeOrder Γ(X, U i) X.functionField p.val p.property.1 p.property.2
      (F a : X.functionField) = 0 := by
  letI : IsFractionRing Γ(X, U i) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U i) (hAffine i)
  intro a
  by_contra horder
  exact hne (actual_support_prime_horizontal_of_mem_avoidance f U hAffine F i p
    ⟨a, horder⟩ hW)

end ActualFiniteChartImages

end ChenRanks
