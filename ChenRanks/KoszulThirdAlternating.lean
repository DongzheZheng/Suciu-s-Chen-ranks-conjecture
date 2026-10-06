import ChenRanks.KoszulThirdObjects

/-! The standard genuine third Koszul formula is actually alternating.
No kernel parameterization or exactness premise is used. -/

noncomputable section

open TensorProduct
open scoped BigOperators TensorProduct

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]

/-- The actual three-term formula is genuinely multilinear.  The library
constructor transports its update identities to every decision procedure. -/
def delta3Multilinear : MultilinearMap k (fun _ : Fin 3 ↦ V) (C2 k V) :=
  MultilinearMap.mk' (fun a ↦
    SymmetricAlgebra.ι k V (a 0) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 1) (a 2)) -
      SymmetricAlgebra.ι k V (a 1) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 0) (a 2)) +
        SymmetricAlgebra.ι k V (a 2) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 0) (a 1)))
    (by
      intro a i x y
      fin_cases i <;>
        simp [Function.update, map_add,
          add_smul, TensorProduct.tmul_add] <;> abel)
    (by
      intro a i c x
      fin_cases i
      · simp [Function.update, map_smul, TensorProduct.tmul_smul, smul_sub, smul_add, smul_assoc]
        rw [smul_comm (SymmetricAlgebra.ι k V (a 1)) c,
          smul_comm (SymmetricAlgebra.ι k V (a 2)) c]
      · simp [Function.update, map_smul, TensorProduct.tmul_smul, smul_sub, smul_add, smul_assoc]
        rw [smul_comm (SymmetricAlgebra.ι k V (a 0)) c,
          smul_comm (SymmetricAlgebra.ι k V (a 2)) c]
      · simp [Function.update, map_smul, TensorProduct.tmul_smul, smul_sub, smul_add, smul_assoc]
        rw [smul_comm (SymmetricAlgebra.ι k V (a 0)) c,
          smul_comm (SymmetricAlgebra.ι k V (a 1)) c])

/-- The standard genuine third Koszul formula is alternating. -/
def delta3Alternating : V [⋀^Fin 3]→ₗ[k] C2 k V where
  toMultilinearMap := delta3Multilinear k V
  map_eq_zero_of_eq' a i j h hij := by
    change delta3Multilinear k V a = 0
    change SymmetricAlgebra.ι k V (a 0) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 1) (a 2)) -
      SymmetricAlgebra.ι k V (a 1) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 0) (a 2)) +
        SymmetricAlgebra.ι k V (a 2) • ((1 : S k V) ⊗ₜ[k] exteriorWedge (a 0) (a 1)) = 0
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      simp only [h, wedgeTwo_self, TensorProduct.tmul_zero, smul_zero, sub_self, zero_add]
    · change a 0 = a 2 at h
      simp only [h, wedgeTwo_self, TensorProduct.tmul_zero, smul_zero, sub_zero]
      rw [wedgeTwo_swap k V (a 1) (a 2), TensorProduct.tmul_neg, smul_neg,
        neg_add_cancel]
    · change a 1 = a 0 at h
      simp only [h, wedgeTwo_self, TensorProduct.tmul_zero, smul_zero, sub_self, zero_add]
    · exact (hij rfl).elim
    · change a 1 = a 2 at h
      simp only [h, wedgeTwo_self, TensorProduct.tmul_zero, smul_zero, zero_sub,
        neg_add_cancel]
    · change a 2 = a 0 at h
      simp only [h, wedgeTwo_self, TensorProduct.tmul_zero, smul_zero, sub_zero]
      rw [wedgeTwo_swap k V (a 1) (a 0), TensorProduct.tmul_neg, smul_neg,
        neg_add_cancel]
    · change a 2 = a 1 at h
      simp only [h, wedgeTwo_self, TensorProduct.tmul_zero, smul_zero, zero_sub,
        neg_add_cancel]
    · exact (hij rfl).elim

end ChenRanks.Koszul
