import ChenRanks.DiscretePrincipalFrameCovering

/-! The actual developing character on the genuine glued total space.

Its definition includes the actual selected frame. In every actual chart,
the same function is the actual local frame character plus the character
of the actual discrete fiber coordinate. The selected index need not be
continuous. Chartwise continuity of the genuine frame characters proves
global continuity; the native monodromy character is the actual endpoint
difference. These are intermediate statements to be instantiated with
the arrangement's constructed frames and proved local derivative.
-/
noncomputable section
namespace ChenRanks.TopologicalComparison
open Set Topology
variable {ι B H V : Type*} [TopologicalSpace B] [Group H]
variable [TopologicalSpace H] [DiscreteTopology H]
variable [AddCommGroup V]
variable (D : DiscretePrincipalFrameCover (ι := ι) (B := B) (H := H))
variable (σ : H →* Multiplicative V)

/-- The actual developing character contains the actual selected frame,
so it is compatible with the native transition functions. -/
def discretePrincipalFrameDevelopingCharacter
    (p : DiscretePrincipalFrameTotalSpace D) : V :=
  Multiplicative.toAdd (σ (D.frame (D.indexAt p.1) p.1 * (show H from p.2)))

/-- The genuine global function has this literal expression in every
native chart, by the actual original group cancellation identity. -/
theorem discretePrincipalFrameDevelopingCharacter_chart
    (i : ι) (p : DiscretePrincipalFrameTotalSpace D) :
    discretePrincipalFrameDevelopingCharacter D σ p =
      Multiplicative.toAdd (σ (D.frame i p.1)) +
      Multiplicative.toAdd (σ (((discretePrincipalFrameCore D).localTriv i p).2)) := by
  change Multiplicative.toAdd (σ (D.frame (D.indexAt p.1) p.1 * (show H from p.2))) =
    Multiplicative.toAdd (σ (D.frame i p.1)) +
      Multiplicative.toAdd (σ ((D.frame i p.1)⁻¹ * D.frame (D.indexAt p.1) p.1 *
        (show H from p.2)))
  rw [← toAdd_mul, ← map_mul]
  simp only [mul_assoc, mul_inv_cancel_left]

variable [TopologicalSpace V] [ContinuousAdd V]

/-- Actual chart characters give actual continuity of the global
developing character, even though the original index selection is arbitrary. -/
theorem discretePrincipalFrameDevelopingCharacter_continuous
    (hframe : ∀ i, ContinuousOn (fun x => Multiplicative.toAdd (σ (D.frame i x)))
      (D.baseSet i)) : Continuous (discretePrincipalFrameDevelopingCharacter D σ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Z := discretePrincipalFrameCore D
  let i := D.indexAt p.1
  have hp : p ∈ (Z.localTriv i).source := D.mem_baseSet_at p.1
  have hlocal : ContinuousAt (Z.localTriv i) p :=
    (Z.localTriv i).toOpenPartialHomeomorph.continuousAt hp
  have hbase : ContinuousAt
      (fun q : DiscretePrincipalFrameTotalSpace D =>
        Multiplicative.toAdd (σ (D.frame i q.1))) p :=
    ((hframe i p.1 (D.mem_baseSet_at p.1)).continuousAt
      ((D.isOpen_baseSet i).mem_nhds (D.mem_baseSet_at p.1))).comp
      Z.continuous_proj.continuousAt
  have hσ : Continuous (fun h : H => Multiplicative.toAdd (σ h)) :=
    continuous_of_discreteTopology
  have hfiber : ContinuousAt
      (fun q : DiscretePrincipalFrameTotalSpace D =>
        Multiplicative.toAdd (σ ((Z.localTriv i q).2))) p :=
    hσ.continuousAt.comp (continuous_snd.continuousAt.comp hlocal)
  have heq : discretePrincipalFrameDevelopingCharacter D σ =
      fun q => Multiplicative.toAdd (σ (D.frame i q.1)) +
        Multiplicative.toAdd (σ ((Z.localTriv i q).2)) := by
    funext q
    exact discretePrincipalFrameDevelopingCharacter_chart D σ i q
  rw [heq]
  exact hbase.add hfiber

/-- On the original fiber the same selected-frame term is common to all
points, leaving exactly the original fiber character. -/
theorem discretePrincipalFrameDevelopingCharacter_fiber (base : B)
    (p : (discretePrincipalFrameProjection D) ⁻¹' {base}) :
    discretePrincipalFrameDevelopingCharacter D σ p.val =
      Multiplicative.toAdd (σ (D.frame (D.indexAt base) base)) +
      Multiplicative.toAdd (σ (discretePrincipalFrameFiberCoordinates D base p)) := by
  have hp : p.val.1 = base := p.property
  change Multiplicative.toAdd (σ (D.frame (D.indexAt p.val.1) p.val.1 *
    (show H from p.val.2))) = _
  rw [map_mul, toAdd_mul, hp]
  rfl

/-- The character of genuine native monodromy is precisely the endpoint
difference of the genuine global developing character. No path integral
or first-term identification is assumed. -/
theorem discretePrincipalFrameDevelopingCharacter_monodromy_difference
    (base : B) (g : FundamentalGroup B base) :
    Multiplicative.toAdd (σ (discretePrincipalFrameMonodromy D base g)) =
      discretePrincipalFrameDevelopingCharacter D σ
        ((discretePrincipalFrame_isCoveringMap D).monodromy g.toPath
          ((discretePrincipalFrameFiberCoordinates D base).symm 1)).val -
      discretePrincipalFrameDevelopingCharacter D σ
        ((discretePrincipalFrameFiberCoordinates D base).symm 1).val := by
  have hσone : Multiplicative.toAdd (σ (1 : H)) = (0 : V) := by
    rw [σ.map_one]
    rfl
  rw [discretePrincipalFrameDevelopingCharacter_fiber,
    discretePrincipalFrameDevelopingCharacter_fiber,
    Equiv.apply_symm_apply, hσone]
  have hm : discretePrincipalFrameMonodromy D base g =
      discretePrincipalFrameFiberCoordinates D base
        ((discretePrincipalFrame_isCoveringMap D).monodromy g.toPath
          ((discretePrincipalFrameFiberCoordinates D base).symm 1)) := rfl
  rw [hm]
  abel

end ChenRanks.TopologicalComparison
