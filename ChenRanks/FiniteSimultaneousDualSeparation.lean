import ChenRanks.ArrangementMeridianBasepoint
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A genuine linear functional separating finitely many original
vectors from an original subspace. The separating functional is
constructed through the actual quotient and simultaneous nonzero
polynomial evaluation; it is not supplied as a hypothesis. -/

noncomputable section
open scoped BigOperators

namespace ChenRanks

variable {k V ι : Type*} [Field k] [Infinite k] [AddCommGroup V]
  [Module k V] [Fintype ι]

/-- Finitely many nonzero vectors admit one actual dual functional
which is nonzero on every one of them, without an independence premise. -/
theorem exists_dual_simultaneously_nonzero (v : ι → V) (hv : ∀ i, v i ≠ 0) :
    ∃ f : Module.Dual k V, ∀ i, f (v i) ≠ 0 := by
  classical
  have hchoose : ∀ i, ∃ f : Module.Dual k V, f (v i) = 1 :=
    fun i => Module.Projective.exists_dual_eq_one k (hv i)
  let φ : ι → Module.Dual k V := fun i => Classical.choose (hchoose i)
  have hφ : ∀ i, φ i (v i) = 1 := fun i => Classical.choose_spec (hchoose i)
  let q : ι → MvPolynomial ι k :=
    fun i => ∑ j, MvPolynomial.C (φ j (v i)) * MvPolynomial.X j
  have hq : ∀ i, q i ≠ 0 := by
    intro i hz
    have heval := congrArg (MvPolynomial.eval (Pi.single i 1)) hz
    have hvalue : MvPolynomial.eval (Pi.single i 1) (q i) = 1 := by
      simp [q, Pi.single_apply, hφ]
    rw [hvalue, map_zero] at heval
    exact one_ne_zero heval
  obtain ⟨y, hy⟩ := mvPolynomial_exists_simultaneous_nonzero_evaluation k ι ι q hq
  let f : Module.Dual k V := ∑ j, y j • φ j
  refine ⟨f, ?_⟩
  intro i
  have hvalue : f (v i) = MvPolynomial.eval y (q i) := by
    simp only [f, q, LinearMap.sum_apply, LinearMap.smul_apply,
      RingHom.id_apply, smul_eq_mul, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hvalue]
  exact hy i

/-- The actual quotient supplies a single functional vanishing on X
and simultaneously detecting every specified vector outside X. -/
theorem exists_dual_vanishing_subspace_simultaneously_nonzero
    (X : Submodule k V) (v : ι → V) (hv : ∀ i, v i ∉ X) :
    ∃ f : Module.Dual k V, (∀ x ∈ X, f x = 0) ∧ ∀ i, f (v i) ≠ 0 := by
  have hquot : ∀ i, X.mkQ (v i) ≠ 0 := by
    intro i hz
    exact hv i ((Submodule.Quotient.mk_eq_zero X).mp hz)
  obtain ⟨f, hf⟩ := exists_dual_simultaneously_nonzero (k := k)
    (fun i => X.mkQ (v i)) hquot
  refine ⟨f.comp X.mkQ, ?_, hf⟩
  intro x hx
  change f (X.mkQ x) = 0
  have hzero : X.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero X).mpr hx
  rw [hzero, map_zero]

end ChenRanks
