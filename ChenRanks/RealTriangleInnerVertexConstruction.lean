import ChenRanks.RealTrianglePlaneCoordinates
import ChenRanks.FiniteAffineSubspaceAvoidanceInBall
import Mathlib.Tactic

/-!
# Genuine nearby inner vertices avoiding the actual finite bad lines

Every interior standard-triangle point has a nonempty open sector
toward each of its actual vertices. Finite affine-line avoidance in
that actual sector constructs the new vertex. No new vertex,
general-position condition, or edge detector is assumed.
-/

noncomputable section

namespace ChenRanks

/-- A genuine positive affine step can be chosen inside every actual
positive-radius ball. The step is strictly less than one. -/
theorem exists_small_positive_affine_step {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : V) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ dist (x + t • (y - x)) x < ε := by
  have hbound : 0 < min 1 (ε / (‖y - x‖ + 1)) :=
    lt_min zero_lt_one (div_pos hε (by positivity))
  obtain ⟨t, ht0, ht⟩ := exists_between hbound
  have ht1 : t < 1 := lt_of_lt_of_le ht (min_le_left _ _)
  have htε : t < ε / (‖y - x‖ + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  refine ⟨t, ht0, ht1, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht0]
  calc
    t * ‖y - x‖ ≤ t * (‖y - x‖ + 1) := by
      apply mul_le_mul_of_nonneg_left _ ht0.le
      linarith
    _ < (ε / (‖y - x‖ + 1)) * (‖y - x‖ + 1) :=
      mul_lt_mul_of_pos_right htε (by positivity)
    _ = ε := div_mul_cancel₀ ε (by positivity)

/-- An actual point in an actual nonempty open set can be perturbed
within that same set to avoid every supplied actual proper translate. -/
theorem exists_point_in_open_avoiding_finite_affine_subspaces
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (S : ι → Submodule ℝ V) (a : ι → V) (hS : ∀ i, S i ≠ ⊤)
    (U : Set V) (hU : IsOpen U) (x : V) (hx : x ∈ U) :
    ∃ z : V, z ∈ U ∧ ∀ i, z - a i ∉ S i := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨z, hz, havoid⟩ :=
    exists_point_avoiding_finite_affine_subspaces_in_ball S a hS x ε hε
  exact ⟨z, hsub hz, havoid⟩

def realTriangleInnerSector (p : stdSimplex ℝ (Fin 3)) (i : Fin 3) : Set ℂ :=
  (⋂ j : Fin 3, {z : ℂ | 0 < complexTriangleCoordinate z j}) ∩
    (⋂ j : Fin 3, {z : ℂ | j = i ∨ complexTriangleCoordinate z j < p j})

theorem realTriangleInnerSector_isOpen (p : stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    IsOpen (realTriangleInnerSector p i) := by
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite (fun j =>
      isOpen_lt continuous_const (complexTriangleCoordinate_continuous j))
  · apply isOpen_iInter_of_finite
    intro j
    by_cases hji : j = i
    · simpa only [hji, true_or, Set.setOf_true] using
        (isOpen_univ : IsOpen (Set.univ : Set ℂ))
    · simpa only [hji, false_or] using
        isOpen_lt (complexTriangleCoordinate_continuous j) continuous_const

/-- The actual open sector meets every actual neighborhood of p.
The witness is a derived positive homothetic step toward vertex i. -/
theorem realTriangleInnerSector_meets_ball (p : stdSimplex ℝ (Fin 3))
    (hp : ∀ j : Fin 3, 0 < p j) (i : Fin 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℂ, z ∈ realTriangleInnerSector p i ∧
      dist z (realTrianglePlaneCoordinate p) < ε := by
  let x := realTrianglePlaneCoordinate p
  let y := realTrianglePlaneCoordinate (stdSimplex.vertex i)
  obtain ⟨t, ht0, ht1, hdist⟩ := exists_small_positive_affine_step x y ε hε
  let z := (1 - t) • x + t • y
  have hz : z = x + t • (y - x) := by
    dsimp only [z]
    rw [sub_smul, one_smul, smul_sub]
    abel
  have hc (j : Fin 3) : complexTriangleCoordinate z j =
      (1 - t) * p j + t * (if j = i then 1 else 0) := by
    dsimp only [z, x, y]
    rw [complexTriangleCoordinate_affine,
      complexTriangleCoordinate_plane, complexTriangleCoordinate_plane]
    simp [stdSimplex.vertex, Pi.single_apply, eq_comm]
  have hpos : ∀ j : Fin 3, 0 < complexTriangleCoordinate z j := by
    intro j
    rw [hc]
    by_cases hji : j = i
    · rw [if_pos hji]
      nlinarith [hp j]
    · rw [if_neg hji, mul_zero, add_zero]
      exact mul_pos (sub_pos.mpr ht1) (hp j)
  refine ⟨z, ?_, ?_⟩
  · constructor
    · exact Set.mem_iInter.mpr hpos
    · apply Set.mem_iInter.mpr
      intro j
      by_cases hji : j = i
      · exact Or.inl hji
      · right
        rw [hc, if_neg hji, mul_zero, add_zero]
        nlinarith [hp j]
  · rwa [hz]

/-- The actual inner vertex is constructed from p and the supplied
actual proper affine subspaces. It is inside the genuine simplex,
arbitrarily close to p, with both other coordinates strictly smaller. -/
theorem exists_realTriangleInnerVertex_avoiding_finite_affine_subspaces
    {ι : Type*} [Fintype ι] (S : ι → Submodule ℝ ℂ) (a : ι → ℂ)
    (hS : ∀ l, S l ≠ ⊤) (p : stdSimplex ℝ (Fin 3))
    (hp : ∀ j : Fin 3, 0 < p j) (i : Fin 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : stdSimplex ℝ (Fin 3),
      (∀ j : Fin 3, 0 < q j) ∧ (∀ j : Fin 3, j ≠ i → q j < p j) ∧
      dist (realTrianglePlaneCoordinate q) (realTrianglePlaneCoordinate p) < ε ∧
      ∀ l, realTrianglePlaneCoordinate q - a l ∉ S l := by
  obtain ⟨z, hz, hzdist⟩ := realTriangleInnerSector_meets_ball p hp i ε hε
  let U := realTriangleInnerSector p i ∩ Metric.ball (realTrianglePlaneCoordinate p) ε
  have hU : IsOpen U := (realTriangleInnerSector_isOpen p i).inter Metric.isOpen_ball
  have hzU : z ∈ U := ⟨hz, hzdist⟩
  obtain ⟨w, hw, havoid⟩ :=
    exists_point_in_open_avoiding_finite_affine_subspaces S a hS U hU z hzU
  have hwpos : ∀ j : Fin 3, 0 < complexTriangleCoordinate w j :=
    Set.mem_iInter.mp hw.1.1
  let q := realTrianglePointOfPlane w (fun j => (hwpos j).le)
  have hq : realTrianglePlaneCoordinate q = w :=
    realTrianglePlaneCoordinate_pointOfPlane w _
  refine ⟨q, hwpos, ?_, ?_, ?_⟩
  · intro j hji
    exact (Set.mem_iInter.mp hw.1.2 j).resolve_left hji
  · rw [hq]
    exact hw.2
  · intro l
    rw [hq]
    exact havoid l

end ChenRanks
