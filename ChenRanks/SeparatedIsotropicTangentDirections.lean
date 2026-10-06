import ChenRanks.SeparatedIsotropicIntersections
import ChenRanks.ResonanceObjects

/-!
# Linear tangent directions under actual exterior separation

For independent vectors `u,v` in an actual subspace `P`, the relation
`α ∧ v + u ∧ β ∈ Λ² P` forces both representatives `α,β` into `P`.
The proof constructs the two separating dual linear forms from genuine
quotients by one-dimensional spans and applies actual exterior contractions.

The application to a Grassmannian tangent space still requires a theorem
identifying its actual tangent functor with this exterior relation. No
Grassmannian scheme, regular local ring, or reducedness theorem is asserted
by this linear-algebra module.
-/

noncomputable section

namespace ChenRanks

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

private theorem tangentExteriorWedge_swap (a b : E) :
    exteriorWedge (k := k) a b = -exteriorWedge (k := k) b a := by
  apply (ExteriorAlgebra.exteriorPower k 2 E).subtype_injective
  change (exteriorWedge (k := k) a b : ExteriorAlgebra k E) =
    -(exteriorWedge (k := k) b a : ExteriorAlgebra k E)
  rw [exteriorWedge_coe, exteriorWedge_coe]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

/-- Linear independence constructs an actual dual form taking value one
on the first vector and zero on the second. Its existence is proved using
the actual quotient by the second vector's span. -/
theorem exists_dual_one_zero_of_pair_independent
    (u v : E) (huv : LinearIndependent k ![u, v]) :
    ∃ ρ : E →ₗ[k] k, ρ u = 1 ∧ ρ v = 0 := by
  have hunot : u ∉ k ∙ v := by
    intro hu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
    have hzero : (1 : k) • u + (-c) • v = 0 := by
      rw [one_smul, ← hc, neg_smul, add_neg_cancel]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp huv) 1 (-c) hzero).1
  let V := k ∙ v
  have huq : V.mkQ u ≠ 0 := by
    intro hzero
    exact hunot ((Submodule.Quotient.mk_eq_zero V).mp hzero)
  obtain ⟨σ, hσ⟩ := _root_.Module.Projective.exists_dual_eq_one k huq
  refine ⟨σ.comp V.mkQ, hσ, ?_⟩
  change σ (V.mkQ v) = 0
  have hvq : V.mkQ v = 0 :=
    (Submodule.Quotient.mk_eq_zero V).mpr (Submodule.mem_span_singleton_self v)
  rw [hvq, map_zero]

/-- The actual pure exterior-square condition eliminates all normal
representatives to an independent pair in P, by two actual contractions. -/
theorem tangent_representatives_mem_of_pure_exterior
    (P : Submodule k E) (u v α β : E) (hu : u ∈ P) (hv : v ∈ P)
    (huv : LinearIndependent k ![u, v])
    (hrel : exteriorWedge (k := k) α v + exteriorWedge u β ∈ pureExterior P) :
    α ∈ P ∧ β ∈ P := by
  obtain ⟨ρu, hρuu, hρuv⟩ := exists_dual_one_zero_of_pair_independent u v huv
  obtain ⟨ρv, hρvv, hρvu⟩ := exists_dual_one_zero_of_pair_independent v u
    (LinearIndependent.pair_symm_iff.mp huv)
  have hcu := pointContraction_pureExterior_mem P ρu hrel
  simp only [map_add, Koszul.pointDeltaTwo_wedge, hρuu, hρuv,
    zero_smul, sub_zero, one_smul] at hcu
  have hbminus : β - ρu β • u ∈ P := by
    simpa using P.sub_mem hcu (P.smul_mem (ρu α) hv)
  have hb : β ∈ P := by
    simpa using P.add_mem hbminus (P.smul_mem (ρu β) hu)
  have hcv := pointContraction_pureExterior_mem P ρv hrel
  simp only [map_add, Koszul.pointDeltaTwo_wedge, hρvv, hρvu,
    one_smul, zero_smul, zero_sub] at hcv
  have haminus : ρv α • v - α ∈ P := by
    simpa [add_assoc] using P.add_mem hcv (P.smul_mem (ρv β) hu)
  have ha : α ∈ P := by
    simpa using P.sub_mem (P.smul_mem (ρv α) hv) haminus
  exact ⟨ha, hb⟩

/-- Actual separation turns the actual linear exterior relation into the
pure exterior-square condition, and hence forces both representatives
into P. No desired dual form or normal-direction detector is an input. -/
theorem tangent_representatives_mem_of_separated_relation
    (I : Submodule k (⋀[k]^2 E)) (P : Submodule k E)
    (hsep : mixedExterior P ⊓ I = pureExterior P)
    (u v α β : E) (hu : u ∈ P) (hv : v ∈ P)
    (huv : LinearIndependent k ![u, v])
    (hrel : exteriorWedge (k := k) α v + exteriorWedge u β ∈ I) :
    α ∈ P ∧ β ∈ P := by
  have hleft : exteriorWedge (k := k) α v ∈ mixedExterior P := by
    rw [tangentExteriorWedge_swap α v]
    exact (mixedExterior P).neg_mem (exteriorWedge_mem_mixed P ⟨v, hv⟩ α)
  have hright : exteriorWedge (k := k) u β ∈ mixedExterior P :=
    exteriorWedge_mem_mixed P ⟨u, hu⟩ β
  have hpure : exteriorWedge (k := k) α v + exteriorWedge u β ∈ pureExterior P := by
    rw [← hsep]
    exact ⟨(mixedExterior P).add_mem hleft hright, hrel⟩
  exact tangent_representatives_mem_of_pure_exterior P u v α β hu hv huv hpure

end ChenRanks
