import ChenRanks.MixedUniverseSymmetricDualSpecialization
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finite actual origin-power quotients in independent universes

This is the actual symmetric ring on the original dual, not a reindexed
replacement. Genuine origin-generator powers in the actual ideal make
the actual quotient generators integral. Native symmetric induction
and actual finite-type algebra then prove base-field finiteness.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E] [FiniteDimensional k E]
variable (J : Ideal (S k (_root_.Module.Dual k E)))

theorem mixedUniverseOriginPowerQuotient_integral (n : ℕ)
    (hn : mixedUniverseSymmetricDualOriginIdeal k E ^ n ≤ J) :
    Algebra.IsIntegral k ((S k (_root_.Module.Dual k E)) ⧸ J) := by
  let q : S k (_root_.Module.Dual k E) →ₐ[k]
      (S k (_root_.Module.Dual k E)) ⧸ J := Ideal.Quotient.mkₐ k J
  refine ⟨?_⟩
  intro z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  change IsIntegral k (q s)
  induction s using SymmetricAlgebra.induction with
  | algebraMap c =>
      rw [AlgHom.commutes]
      exact isIntegral_algebraMap
  | ι φ =>
      have hφ : SymmetricAlgebra.ι k (_root_.Module.Dual k E) φ ∈
          mixedUniverseSymmetricDualOriginIdeal k E :=
        Ideal.subset_span (Set.mem_range_self φ)
      have hφn := hn (Ideal.pow_mem_pow hφ n)
      have hz : q (SymmetricAlgebra.ι k (_root_.Module.Dual k E) φ) ^ n = 0 := by
        rw [← map_pow]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hφn
      apply IsIntegral.of_pow (Nat.succ_pos n)
      rw [pow_succ, hz, zero_mul]
      exact isIntegral_zero
  | mul s t hs ht =>
      rw [map_mul]
      exact hs.mul ht
  | add s t hs ht =>
      rw [map_add]
      exact hs.add ht

theorem mixedUniverseOriginPowerQuotient_finite (n : ℕ)
    (hn : mixedUniverseSymmetricDualOriginIdeal k E ^ n ≤ J) :
    _root_.Module.Finite k ((S k (_root_.Module.Dual k E)) ⧸ J) := by
  letI := mixedUniverse_symmetricDual_finiteType k E
  letI := mixedUniverseOriginPowerQuotient_integral k E J n hn
  exact Algebra.IsIntegral.finite

end ChenRanks.Koszul
