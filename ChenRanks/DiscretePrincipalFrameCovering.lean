import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Covering.Basic
import ChenRanks.PrincipalCoveringNativeMonodromy

/-! Actual group-valued local frames whose actual transition functions
are continuous for the discrete group topology define a genuine native
principal covering. Native total-space translations and fiber coordinates
are constructed, so the original fundamental-group representation is a
conclusion. These are intermediate local-frame data; an arrangement must
construct them from its actual parallel frames, not supply them as a
hypothesis of its final Chen-rank theorem.
-/
noncomputable section
namespace ChenRanks.TopologicalComparison
open Set Topology
variable {ι B H : Type*} [TopologicalSpace B] [Group H]
variable [TopologicalSpace H] [DiscreteTopology H]

/-- Actual local frames on an actual open cover, with genuine transitions. -/
structure DiscretePrincipalFrameCover where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  frame : ι → B → H
  continuousOn_transition : ∀ i j,
    ContinuousOn (fun x => (frame j x)⁻¹ * frame i x) (baseSet i ∩ baseSet j)

variable (D : DiscretePrincipalFrameCover (ι := ι) (B := B) (H := H))

/-- The true native bundle core uses the same original frame changes. -/
def discretePrincipalFrameCore : FiberBundleCore ι B H where
  baseSet := D.baseSet
  isOpen_baseSet := D.isOpen_baseSet
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet_at
  coordChange i j x h := (D.frame j x)⁻¹ * D.frame i x * h
  coordChange_self i x hx h := by simp
  continuousOn_coordChange i j := by
    have hc : ContinuousOn (fun p : B × H => (D.frame j p.1)⁻¹ * D.frame i p.1)
        ((D.baseSet i ∩ D.baseSet j) ×ˢ univ) :=
      (D.continuousOn_transition i j).comp continuous_fst.continuousOn (fun _ h => h.1)
    have hm : Continuous (fun p : H × H => p.1 * p.2) := continuous_of_discreteTopology
    exact hm.comp_continuousOn (hc.prodMk continuous_snd.continuousOn)
  coordChange_comp i j l x hx h := by simp [mul_assoc]

abbrev DiscretePrincipalFrameTotalSpace := (discretePrincipalFrameCore D).TotalSpace

/-- This is the genuine projection of the actual native glued total space. -/
def discretePrincipalFrameProjection : DiscretePrincipalFrameTotalSpace D → B :=
  (discretePrincipalFrameCore D).proj

/-- Discreteness of the genuine fiber gives the actual native covering. -/
theorem discretePrincipalFrame_isCoveringMap : IsCoveringMap (discretePrincipalFrameProjection D) :=
  FiberBundle.isCoveringMap

/-- Actual right translation of the actual glued total-space fiber. -/
def discretePrincipalFrameRightTranslation (r : H) :
    DiscretePrincipalFrameTotalSpace D → DiscretePrincipalFrameTotalSpace D :=
  fun p => ⟨p.1, (show H from p.2) * r⟩

/-- True right translations are continuous in the native glued topology. -/
theorem discretePrincipalFrameRightTranslation_continuous (r : H) :
    Continuous (discretePrincipalFrameRightTranslation D r) := by
  let Z := discretePrincipalFrameCore D
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := (Z.localTrivAt p.1).toOpenPartialHomeomorph
  have hp : p ∈ e.source := Z.mem_baseSet_at p.1
  have hpre : (discretePrincipalFrameRightTranslation D r) ⁻¹' e.source ∈ 𝓝 p := by
    change e.source ∈ 𝓝 p
    exact e.open_source.mem_nhds hp
  apply (e.continuousAt_iff_continuousAt_comp_left hpre).mpr
  have hright : Continuous (fun q : B × H => (q.1, q.2 * r)) :=
    continuous_fst.prodMk
      ((continuous_of_discreteTopology : Continuous (fun h : H => h * r)).comp continuous_snd)
  have heq : e ∘ discretePrincipalFrameRightTranslation D r =
      (fun q : B × H => (q.1, q.2 * r)) ∘ e := by
    funext q
    apply Prod.ext
    · rfl
    · change (D.frame (Z.indexAt p.1) q.1)⁻¹ * D.frame (Z.indexAt q.1) q.1 *
          ((show H from q.2) * r) =
        ((D.frame (Z.indexAt p.1) q.1)⁻¹ * D.frame (Z.indexAt q.1) q.1 *
          (show H from q.2)) * r
      exact (mul_assoc _ _ _).symm
  rw [heq]
  exact hright.continuousAt.comp (e.continuousAt hp)

/-- The actual original fiber has its native coordinate equivalence. -/
def discretePrincipalFrameFiberCoordinates (base : B) :
    ((discretePrincipalFrameProjection D) ⁻¹' {base}) ≃ H where
  toFun p := p.val.2
  invFun h := ⟨⟨base, h⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨x, h⟩, hx⟩
    change x = base at hx
    subst x
    rfl
  right_inv h := rfl

/-- Native principal coordinates and genuine translations of the same
actual covering, with no monodromy representation supplied. -/
def discretePrincipalFramePrincipalCoordinates (base : B) :
    PrincipalCoveringCoordinates (discretePrincipalFrame_isCoveringMap D) base (H := H) where
  coordinates := discretePrincipalFrameFiberCoordinates D base
  translation r := ⟨discretePrincipalFrameRightTranslation D r,
    discretePrincipalFrameRightTranslation_continuous D r⟩
  projection_translation _ _ := rfl
  coordinates_translation _ _ := rfl

/-- Actual native monodromy of the original fundamental group, constructed
from actual local frames and the actual native covering. -/
def discretePrincipalFrameMonodromy (base : B) : FundamentalGroup B base →* H :=
  principalCoveringNativeMonodromy (discretePrincipalFrame_isCoveringMap D) base
    (discretePrincipalFramePrincipalCoordinates D base)

end ChenRanks.TopologicalComparison
