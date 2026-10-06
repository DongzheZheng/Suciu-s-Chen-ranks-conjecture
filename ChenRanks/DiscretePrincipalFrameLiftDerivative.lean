import ChenRanks.DiscretePrincipalFrameDevelopingCharacter
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Genuine differentiation along a continuous lift in the native principal cover.

The discrete coordinate of an actual continuous lift is proved locally
constant in an actual native chart.  Consequently the actual developing
character is, near that parameter, the actual local frame character plus
a constant.  Native differentiation therefore uses only the derivative
of the actual base curve and the actual local frame primitive.

The local primitive identity is an intermediate interface; the arrangement
application derives it from its constructed finite parallel functions.
Neither local constancy, differentiability of a lift in a manifold
structure, an integral identity, nor a monodromy period is assumed.
-/

noncomputable section

namespace ChenRanks.TopologicalComparison

open Set Topology Filter

variable {ι B H X : Type*} [TopologicalSpace B] [Group H]
variable [TopologicalSpace H] [DiscreteTopology H]
variable (D : DiscretePrincipalFrameCover (ι := ι) (B := B) (H := H))

variable [TopologicalSpace X]

/-- Actual continuity and an actual native chart imply local constancy
of the original discrete fiber coordinate. -/
theorem discretePrincipalFrameLift_coordinate_eventuallyEq
    (g : X → DiscretePrincipalFrameTotalSpace D) (t : X)
    (hg : ContinuousAt g t) (i : ι) (ht : (g t).1 ∈ D.baseSet i) :
    (fun z => ((discretePrincipalFrameCore D).localTriv i (g z)).2) =ᶠ[𝓝 t]
      fun _ => ((discretePrincipalFrameCore D).localTriv i (g t)).2 := by
  let e := ((discretePrincipalFrameCore D).localTriv i).toOpenPartialHomeomorph
  have hge : ContinuousAt (fun z => e (g z)) t :=
    (e.continuousAt ht).comp hg
  have hcoord : ContinuousAt (fun z => (e (g z)).2) t :=
    continuous_snd.continuousAt.comp hge
  have hsingleton : ({(e (g t)).2} : Set H) ∈ 𝓝 ((e (g t)).2) :=
    (isOpen_discrete _).mem_nhds (by rfl)
  exact hcoord.eventually_mem hsingleton

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (σ : H →* Multiplicative V) (κ : B → E)

/-- In a genuine chart, the actual developing function along the actual
continuous lift equals the actual local primitive plus one actual
constant discrete-coordinate character near the parameter. -/
theorem discretePrincipalFrameLift_eventuallyEq_localPrimitive
    (g : X → DiscretePrincipalFrameTotalSpace D) (t : X)
    (hg : ContinuousAt g t) (i : ι) (ht : (g t).1 ∈ D.baseSet i)
    (P : E → V)
    (hP : ∀ x ∈ D.baseSet i, Multiplicative.toAdd (σ (D.frame i x)) = P (κ x)) :
    (fun z => discretePrincipalFrameDevelopingCharacter D σ (g z)) =ᶠ[𝓝 t]
      fun z => P (κ (g z).1) +
        Multiplicative.toAdd
          (σ (((discretePrincipalFrameCore D).localTriv i (g t)).2)) := by
  have hbase : ContinuousAt (fun z => (g z).1) t :=
    (discretePrincipalFrameCore D).continuous_proj.continuousAt.comp hg
  have hmem : ∀ᶠ z in 𝓝 t, (g z).1 ∈ D.baseSet i :=
    hbase.eventually_mem ((D.isOpen_baseSet i).mem_nhds ht)
  have hcoord := discretePrincipalFrameLift_coordinate_eventuallyEq D g t hg i ht
  filter_upwards [hmem, hcoord] with z hz hc
  rw [discretePrincipalFrameDevelopingCharacter_chart D σ i (g z), hP _ hz, hc]

/-- Genuine native differentiation of the developing character along
an actual continuous lift.  Discrete-coordinate constancy is derived,
and there is no period or integral premise. -/
theorem discretePrincipalFrameLift_hasDerivAt
    (g : ℝ → DiscretePrincipalFrameTotalSpace D) (t : ℝ)
    (hg : ContinuousAt g t) (i : ι) (ht : (g t).1 ∈ D.baseSet i)
    (P : E → V)
    (hP : ∀ x ∈ D.baseSet i, Multiplicative.toAdd (σ (D.frame i x)) = P (κ x))
    (P' : E →L[ℝ] V) (hP' : HasFDerivAt P P' (κ (g t).1))
    (u : E) (hu : HasDerivAt (fun z => κ (g z).1) u t) :
    HasDerivAt (fun z => discretePrincipalFrameDevelopingCharacter D σ (g z))
      (P' u) t := by
  have h := (hP'.comp_hasDerivAt t hu).add_const
    (Multiplicative.toAdd
      (σ (((discretePrincipalFrameCore D).localTriv i (g t)).2)))
  exact h.congr_of_eventuallyEq
    (discretePrincipalFrameLift_eventuallyEq_localPrimitive D σ κ g t hg i ht P hP)

/-- The same genuine derivative within a real parameter set. This
version includes endpoints needed by native interval integration. -/
theorem discretePrincipalFrameLift_hasDerivWithinAt
    (g : ℝ → DiscretePrincipalFrameTotalSpace D) (t : ℝ) (s : Set ℝ)
    (hg : ContinuousAt g t) (i : ι) (ht : (g t).1 ∈ D.baseSet i)
    (P : E → V)
    (hP : ∀ x ∈ D.baseSet i, Multiplicative.toAdd (σ (D.frame i x)) = P (κ x))
    (P' : E →L[ℝ] V) (hP' : HasFDerivAt P P' (κ (g t).1))
    (u : E) (hu : HasDerivWithinAt (fun z => κ (g z).1) u s t) :
    HasDerivWithinAt (fun z => discretePrincipalFrameDevelopingCharacter D σ (g z))
      (P' u) s t := by
  have h := (hP'.comp_hasDerivWithinAt t hu).add_const
    (Multiplicative.toAdd
      (σ (((discretePrincipalFrameCore D).localTriv i (g t)).2)))
  have heq := discretePrincipalFrameLift_eventuallyEq_localPrimitive
    D σ κ g t hg i ht P hP
  have hpoint : discretePrincipalFrameDevelopingCharacter D σ (g t) =
      P (κ (g t).1) + Multiplicative.toAdd
        (σ (((discretePrincipalFrameCore D).localTriv i (g t)).2)) := by
    rw [discretePrincipalFrameDevelopingCharacter_chart D σ i (g t), hP _ ht]
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) hpoint

end ChenRanks.TopologicalComparison
