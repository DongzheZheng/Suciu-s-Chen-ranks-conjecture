import ChenRanks.ArrangementHyperplaneRegularPaths
import ChenRanks.ArrangementPathUniformNeighborhood
import ChenRanks.ArrangementMeridianCircle
import ChenRanks.SingularSquareCocycleHomotopy

/-!
# Actual continuous transverse families at regular hyperplane points

A transverse family is an actual continuous map on I × ℂ which sends
zero to zero and whose distinguished original equation is the actual
complex parameter. The compact zero section lies in the actual open
set avoiding every other original hyperplane. Its positive thickening
therefore constructs actual small circle boundaries and a genuine free
homotopy. The construction applies to complex-linear or real-linear
transverse planes and does not assume a meridian class equality.
-/

noncomputable section

open unitInterval

namespace ChenRanks.AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

local instance transverseMeridianFamilyLabelDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Compactness of the genuine zero section derives an actual radius
for a genuine continuous family of local transverse lifts. -/
theorem exists_actual_transverse_family_radius (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : I) (z : ℂ), ‖z‖ ≤ r →
      ∀ K : ι, K ≠ H →
        A.normal K ((γ t).val + T (t, z)) ≠ A.offset K := by
  let U : Set (I × ℂ) := ⋂ K : {K : ι // K ≠ H},
    {p | A.normal K.val ((γ p.1).val + T p) ≠ A.offset K.val}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro K
    apply isOpen_ne_fun _ continuous_const
    exact (A.normal K.val).continuous_of_finiteDimensional.comp
      ((continuous_subtype_val.comp (γ.continuous.comp continuous_fst)).add T.continuous)
  let c : I → I × ℂ := fun t => (t, 0)
  have hc : Continuous c := continuous_id.prodMk continuous_const
  have hK : IsCompact (Set.range c) := isCompact_range hc
  have hKU : Set.range c ⊆ U := by
    rintro _ ⟨t, rfl⟩
    apply Set.mem_iInter.mpr
    intro K
    change A.normal K.val ((γ t).val + T (t, 0)) ≠ A.offset K.val
    rw [hzero t, add_zero]
    exact (γ t).property.2 K.val K.property
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t z hz K hKH
  have hd : dist (t, z) (c t) < ε := by
    change dist (t, z) (t, (0 : ℂ)) < ε
    rw [dist_prod_same_left, dist_zero_right]
    exact hz.trans_lt (half_lt_self hε)
  exact Set.mem_iInter.mp
    (hεU (Metric.mem_thickening_iff.mpr ⟨c t, ⟨t, rfl⟩, hd⟩)) ⟨K, hKH⟩

/-- Choose from the actual positive-radius proof, never from a tube premise. -/
def actualTransverseFamilyRadius (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0) : ℝ :=
  (A.exists_actual_transverse_family_radius H γ T hzero).choose

theorem actualTransverseFamilyRadius_pos (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0) :
    0 < A.actualTransverseFamilyRadius H γ T hzero :=
  (A.exists_actual_transverse_family_radius H γ T hzero).choose_spec.1

theorem actualTransverseFamilyRadius_avoids (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (t : I) (z : ℂ)
    (hz : ‖z‖ ≤ A.actualTransverseFamilyRadius H γ T hzero)
    (K : ι) (hKH : K ≠ H) :
    A.normal K ((γ t).val + T (t, z)) ≠ A.offset K :=
  (A.exists_actual_transverse_family_radius H γ T hzero).choose_spec.2
    t z hz K hKH

/-- The actual circle homotopy in the original complement. The
transverse equation is a genuine map identity, not an assigned winding. -/
def transverseFamilyCircleHomotopy (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (htransverse : ∀ (t : I) (z : ℂ), A.normal H (T (t, z)) = z) :
    C(I × Circle, A.Complement) where
  toFun p := ⟨(γ p.1).val +
      T (p.1, (A.actualTransverseFamilyRadius H γ T hzero : ℂ) * (p.2 : ℂ)), by
    intro K
    by_cases hKH : K = H
    · subst K
      rw [map_add, (γ p.1).property.1, htransverse]
      intro heq
      have hz : (A.actualTransverseFamilyRadius H γ T hzero : ℂ) *
          (p.2 : ℂ) = 0 :=
        add_left_cancel (heq.trans (add_zero (A.offset H)).symm)
      exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (A.actualTransverseFamilyRadius_pos H γ T hzero).ne')
        p.2.coe_ne_zero hz
    · apply A.actualTransverseFamilyRadius_avoids H γ T hzero p.1 _ _ K hKH
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
        abs_of_pos (A.actualTransverseFamilyRadius_pos H γ T hzero), mul_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (γ.continuous.comp continuous_fst)).add
      (T.continuous.comp
        (continuous_fst.prodMk (continuous_const.mul
          (continuous_subtype_val.comp continuous_snd))))

/-- The actual interval loop at an actual parameter value of the family. -/
def transverseFamilyPath (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (htransverse : ∀ (t : I) (z : ℂ), A.normal H (T (t, z)) = z) (s : I) :
    C(I, A.Complement) :=
  (A.transverseFamilyCircleHomotopy H γ T hzero htransverse).comp
    ⟨fun t => (s, positiveUnitCircleTraversal t),
      continuous_const.prodMk positiveUnitCircleTraversal.continuous⟩

theorem transverseFamilyPath_endpoints (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (htransverse : ∀ (t : I) (z : ℂ), A.normal H (T (t, z)) = z) (s : I) :
    A.transverseFamilyPath H γ T hzero htransverse s 0 =
      A.transverseFamilyPath H γ T hzero htransverse s 1 := by
  change A.transverseFamilyCircleHomotopy H γ T hzero htransverse
      (s, positiveUnitCircleTraversal 0) =
    A.transverseFamilyCircleHomotopy H γ T hzero htransverse
      (s, positiveUnitCircleTraversal 1)
  rw [positiveUnitCircleTraversal_zero, positiveUnitCircleTraversal_one]

/-- Circle coordinate first, homotopy coordinate second, as used by
the genuine square cocycle relation. -/
def transverseFamilyFreeHomotopy (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (htransverse : ∀ (t : I) (z : ℂ), A.normal H (T (t, z)) = z) :
    C(I × I, A.Complement) :=
  (A.transverseFamilyCircleHomotopy H γ T hzero htransverse).comp
    ⟨fun p => (p.2, positiveUnitCircleTraversal p.1),
      continuous_snd.prodMk
        (positiveUnitCircleTraversal.continuous.comp continuous_fst)⟩

theorem transverseFamilyFreeHomotopy_periodic (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (htransverse : ∀ (t : I) (z : ℂ), A.normal H (T (t, z)) = z) (s : I) :
    A.transverseFamilyFreeHomotopy H γ T hzero htransverse (1, s) =
      A.transverseFamilyFreeHomotopy H γ T hzero htransverse (0, s) := by
  change A.transverseFamilyCircleHomotopy H γ T hzero htransverse
      (s, positiveUnitCircleTraversal 1) =
    A.transverseFamilyCircleHomotopy H γ T hzero htransverse
      (s, positiveUnitCircleTraversal 0)
  rw [positiveUnitCircleTraversal_one, positiveUnitCircleTraversal_zero]

/-- The real square cocycle identity proves equality of actual
closed-cochain values on the actual endpoint circles. -/
theorem transverseFamily_closedCochain_values_eq (H : ι)
    (γ : C(I, A.HyperplaneRegularLocus H))
    (T : C(I × ℂ, Fin d → ℂ)) (hzero : ∀ t : I, T (t, 0) = 0)
    (htransverse : ∀ (t : I) (z : ℂ), A.normal H (T (t, z)) = z)
    (k : Type) [Field k] (a : SingularCohomology.cochains k A.Complement 1)
    (ha : SingularCohomology.differential k A.Complement 1 a = 0) :
    SingularCohomology.values k A.Complement 1 a
        (SingularCohomology.simplexOfPath A.Complement
          (A.transverseFamilyPath H γ T hzero htransverse 0)) =
      SingularCohomology.values k A.Complement 1 a
        (SingularCohomology.simplexOfPath A.Complement
          (A.transverseFamilyPath H γ T hzero htransverse 1)) := by
  exact SingularCohomology.closedCochain_values_squareBottom_eq_top
    A.Complement k (A.transverseFamilyFreeHomotopy H γ T hzero htransverse)
    (A.transverseFamilyFreeHomotopy_periodic H γ T hzero htransverse) a ha

end ChenRanks.AffineArrangement
