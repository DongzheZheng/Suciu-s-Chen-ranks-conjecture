import ChenRanks.ArrangementMeridianBasepoint
import ChenRanks.ArrangementEquationPhaseMaps
import ChenRanks.CirclePathIntegerIncrement
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-! Uncompiled preparation, outside the active Lean inventory.

The genuine pivot-coordinate construction first supplies a point on H
and outside every other hyperplane, and a genuine normal vector. The
other equations are continuous and nonzero at the disk center. Their
finite intersection therefore contains a small actual complex disk.
Its boundary is an actual loop in the original arrangement complement.
The H equation is computed exactly, not assigned an integer label.
-/

noncomputable section

open unitInterval

namespace ChenRanks

/-- The actual unit-circle traversal, parametrized by the real unit
interval and the genuine exponential covering map. -/
def positiveUnitCircleTraversal : C(I, Circle) :=
  Circle.exp.comp ⟨fun t => (2 * Real.pi) * (t : ℝ), by fun_prop⟩

@[simp]
theorem positiveUnitCircleTraversal_zero : positiveUnitCircleTraversal 0 = 1 := by
  simp [positiveUnitCircleTraversal]

@[simp]
theorem positiveUnitCircleTraversal_one : positiveUnitCircleTraversal 1 = 1 := by
  simp [positiveUnitCircleTraversal, Circle.exp_two_pi]

/-- Positive real scaling preserves the actual equation's circle phase. -/
theorem nonzeroComplexCircleMap_positive_real_mul
    (r : ℝ) (hr : 0 < r) (u : Circle) :
    nonzeroComplexCircleMap
      ⟨(r : ℂ) * (u : ℂ),
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') u.coe_ne_zero⟩ = u := by
  change Circle.exp (Complex.arg ((r : ℂ) * (u : ℂ))) = u
  rw [Complex.arg_real_mul _ hr]
  exact Circle.exp_arg u

namespace AffineArrangement

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

/-- Actual geometric data of a small transverse disk. All fields are
proved for the original normal maps and offsets by the constructor. -/
structure MeridianDisk (H : ι) where
  center : Fin d → ℂ
  normalVector : Fin d → ℂ
  center_on : A.normal H center = A.offset H
  center_avoids : ∀ K : ι, K ≠ H → A.normal K center ≠ A.offset K
  normal_value : A.normal H normalVector = 1
  radius : ℝ
  radius_pos : 0 < radius
  disk_avoids : ∀ z : ℂ, ‖z‖ ≤ radius →
    ∀ K : ι, K ≠ H → A.normal K (center + z • normalVector) ≠ A.offset K

/-- The actual small disk is constructed from the actual hyperplanes.
The finite avoidance condition is proved using their continuity at the
constructed center; no disk or radius is supplied as a hypothesis. -/
theorem actualMeridianDisk_nonempty (H : ι) : Nonempty (A.MeridianDisk H) := by
  classical
  obtain ⟨x, hxH, hxother⟩ := A.exists_actual_meridian_center H
  obtain ⟨n, hn⟩ := A.exists_actual_meridian_normal_vector H
  let U : Set ℂ := ⋂ K : {K : ι // K ≠ H},
    {z : ℂ | A.normal K (x + z • n) ≠ A.offset K}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro K
    apply isOpen_ne_fun _ continuous_const
    exact (A.normal K).continuous_of_finiteDimensional.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : (0 : ℂ) ∈ U := by
    apply Set.mem_iInter.mpr
    intro K
    change A.normal K (x + (0 : ℂ) • n) ≠ A.offset K
    simpa using hxother K K.property
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 hzero
  refine ⟨{
    center := x
    normalVector := n
    center_on := hxH
    center_avoids := hxother
    normal_value := hn
    radius := ε / 2
    radius_pos := half_pos hε
    disk_avoids := ?_ }⟩
  intro z hz K hKH
  have hzε : z ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz (half_lt_self hε)
  exact Set.mem_iInter.mp (hεU hzε) ⟨K, hKH⟩

/-- Choose from the proved nonempty actual disk construction. -/
def actualMeridianDisk (H : ι) : A.MeridianDisk H :=
  Classical.choice (A.actualMeridianDisk_nonempty H)

/-- The boundary of the proved actual transverse disk lies in the
actual complement for every point of the actual circle. -/
def meridianDiskCircleMap (H : ι) (m : A.MeridianDisk H) :
    C(Circle, A.Complement) where
  toFun u := ⟨m.center + ((m.radius : ℂ) * (u : ℂ)) • m.normalVector, by
    intro K
    by_cases hKH : K = H
    · subst K
      rw [map_add, map_smul, m.center_on, m.normal_value, smul_eq_mul, mul_one]
      intro hzero
      have hz : (m.radius : ℂ) * (u : ℂ) = 0 := by
        exact add_left_cancel (hzero.trans (add_zero (A.offset H)).symm)
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr m.radius_pos.ne')
        u.coe_ne_zero hz
    · apply m.disk_avoids _ _ K hKH
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
        abs_of_pos m.radius_pos, mul_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add
      ((continuous_const.mul continuous_subtype_val).smul continuous_const)

/-- The distinguished original equation on the actual meridian is
literally radius times the original unit-circle parameter. -/
theorem meridianDiskCircleMap_equation (H : ι) (m : A.MeridianDisk H) (u : Circle) :
    (A.equationComplementNonzeroComplexMap H (A.meridianDiskCircleMap H m u) : ℂ) =
      (m.radius : ℂ) * (u : ℂ) := by
  change A.normal H
    (m.center + ((m.radius : ℂ) * (u : ℂ)) • m.normalVector) - A.offset H = _
  rw [map_add, map_smul, m.center_on, m.normal_value, smul_eq_mul, mul_one]
  ring

/-- Therefore its actual distinguished equation phase is the identity
circle map, rather than a formally assigned meridian coordinate. -/
theorem meridianDiskCircleMap_phase (H : ι) (m : A.MeridianDisk H) (u : Circle) :
    A.equationComplementCircleMap H (A.meridianDiskCircleMap H m u) = u := by
  have heq : A.equationComplementNonzeroComplexMap H (A.meridianDiskCircleMap H m u) =
      ⟨(m.radius : ℂ) * (u : ℂ),
        mul_ne_zero (Complex.ofReal_ne_zero.mpr m.radius_pos.ne') u.coe_ne_zero⟩ :=
    Subtype.ext (A.meridianDiskCircleMap_equation H m u)
  change nonzeroComplexCircleMap
    (A.equationComplementNonzeroComplexMap H (A.meridianDiskCircleMap H m u)) = u
  rw [heq]
  exact nonzeroComplexCircleMap_positive_real_mul m.radius m.radius_pos u

/-- The actual positively oriented meridian path in the actual
arrangement complement. -/
def meridianDiskPathMap (H : ι) (m : A.MeridianDisk H) : C(I, A.Complement) :=
  (A.meridianDiskCircleMap H m).comp positiveUnitCircleTraversal

/-- Its endpoints are equal by the actual exponential period. -/
theorem meridianDiskPathMap_endpoints (H : ι) (m : A.MeridianDisk H) :
    A.meridianDiskPathMap H m 0 = A.meridianDiskPathMap H m 1 := by
  simp [meridianDiskPathMap]

/-- The distinguished original equation has actual winding one on
the proved actual loop, by the genuine covering-space lift. -/
theorem meridianDiskPathMap_distinguished_increment (H : ι) (m : A.MeridianDisk H) :
    circlePathIntegerIncrement
      ((A.equationComplementCircleMap H).comp (A.meridianDiskPathMap H m)) = 1 := by
  have heq : (A.equationComplementCircleMap H).comp (A.meridianDiskPathMap H m) =
      positiveUnitCircleTraversal := by
    apply ContinuousMap.ext
    intro t
    exact A.meridianDiskCircleMap_phase H m (positiveUnitCircleTraversal t)
  rw [heq]
  exact circlePathIntegerIncrement_of_exp_path
    ⟨fun t => (2 * Real.pi) * (t : ℝ), by fun_prop⟩ 1
    (by simp) (by simp)

end AffineArrangement

end ChenRanks
