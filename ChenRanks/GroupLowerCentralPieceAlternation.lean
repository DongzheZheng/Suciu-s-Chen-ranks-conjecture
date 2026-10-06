import ChenRanks.GroupLowerCentralPieceBracket

/-!
# Antisymmetry and alternation of the graded group bracket

Degree reindexing preserves the subgroup and filtration defining each
lower-central quotient.
-/

noncomputable section

open scoped commutatorElement TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

def lowerCentralPieceReindex {r s : ℕ} (h : r = s) :
    lowerCentralPiece G r ≃* lowerCentralPiece G s := by
  cases h
  exact MulEquiv.refl _

theorem lowerCentralPieceReindex_mk_ambient {r s : ℕ} (h : r = s)
    (g : lowerCentralSeries G r) :
    lowerCentralPieceAmbientHom G s
      (lowerCentralPieceReindex G h (QuotientGroup.mk' (nextLowerCentralIn G r) g)) =
      QuotientGroup.mk' (lowerCentralSeries G (s + 1)) (g : G) := by
  cases h
  rfl

def lowerCentralPieceIntReindex {r s : ℕ} (h : r = s) :
    Additive (lowerCentralPiece G r) ≃ₗ[ℤ] Additive (lowerCentralPiece G s) := by
  cases h
  exact LinearEquiv.refl ℤ _

@[simp]
theorem lowerCentralPieceIntReindex_ofMul {r s : ℕ} (h : r = s)
    (g : lowerCentralPiece G r) :
    lowerCentralPieceIntReindex G h (Additive.ofMul g) =
      Additive.ofMul (lowerCentralPieceReindex G h g) := by
  cases h
  rfl

def rationalLowerCentralPieceReindex {r s : ℕ} (h : r = s) :
    rationalLowerCentralPiece G r ≃ₗ[ℚ] rationalLowerCentralPiece G s := by
  cases h
  exact LinearEquiv.refl ℚ _

@[simp]
theorem rationalLowerCentralPieceReindex_tmul {r s : ℕ} (h : r = s)
    (c : ℚ) (g : Additive (lowerCentralPiece G r)) :
    rationalLowerCentralPieceReindex G h (c ⊗ₜ[ℤ] g) =
      c ⊗ₜ[ℤ] (lowerCentralPieceIntReindex G h g) := by
  cases h
  rfl

/-- Original commutator inversion proves actual graded antisymmetry. -/
theorem lowerCentralPieceBracket_swap (m n : ℕ)
    (g : lowerCentralPiece G m) (h : lowerCentralPiece G n) :
    lowerCentralPieceReindex G (show n + m + 1 = m + n + 1 by omega)
      (lowerCentralPieceBracket G n m h g) =
      (lowerCentralPieceBracket G m n g h)⁻¹ := by
  refine QuotientGroup.induction_on g fun g => ?_
  refine QuotientGroup.induction_on h fun h => ?_
  change lowerCentralPieceReindex G _
      (lowerCentralPieceBracket G n m
        (QuotientGroup.mk' (nextLowerCentralIn G n) h)
        (QuotientGroup.mk' (nextLowerCentralIn G m) g)) =
    (lowerCentralPieceBracket G m n
      (QuotientGroup.mk' (nextLowerCentralIn G m) g)
      (QuotientGroup.mk' (nextLowerCentralIn G n) h))⁻¹
  apply lowerCentralPieceAmbientHom_injective G (m + n + 1)
  rw [lowerCentralPieceBracket_mk_mk, lowerCentralPieceBracket_mk_mk,
    lowerCentralPieceReindex_mk_ambient, map_inv,
    lowerCentralPieceAmbientHom_mk]
  change QuotientGroup.mk' (lowerCentralSeries G (m + n + 1 + 1))
      ⁅(h : G), (g : G)⁆ =
    (QuotientGroup.mk' (lowerCentralSeries G (m + n + 1 + 1))
      ⁅(g : G), (h : G)⁆)⁻¹
  rw [← commutatorElement_inv (g : G) (h : G), map_inv]

/-- Antisymmetry is retained on the original additive quotients. -/
theorem lowerCentralPieceBracketAdd_swap (m n : ℕ)
    (g : Additive (lowerCentralPiece G m)) (h : Additive (lowerCentralPiece G n)) :
    lowerCentralPieceIntReindex G (show n + m + 1 = m + n + 1 by omega)
      (lowerCentralPieceBracketAdd G n m h g) =
      -lowerCentralPieceBracketAdd G m n g h := by
  change lowerCentralPieceIntReindex G _
      (Additive.ofMul (lowerCentralPieceBracket G n m (Additive.toMul h) (Additive.toMul g))) =
    Additive.ofMul ((lowerCentralPieceBracket G m n (Additive.toMul g) (Additive.toMul h))⁻¹)
  rw [lowerCentralPieceIntReindex_ofMul]
  exact congrArg Additive.ofMul
    (lowerCentralPieceBracket_swap G m n (Additive.toMul g) (Additive.toMul h))

/-- The diagonal class vanishes over the integers directly from the
original self-commutator, without dividing by two. -/
theorem lowerCentralPieceBracketAdd_self (m : ℕ)
    (g : Additive (lowerCentralPiece G m)) :
    lowerCentralPieceBracketAdd G m m g g = 0 := by
  change Additive.ofMul
    (lowerCentralPieceBracket G m m (Additive.toMul g) (Additive.toMul g)) = 0
  suffices h : lowerCentralPieceBracket G m m
      (Additive.toMul g) (Additive.toMul g) = 1 by
    exact congrArg Additive.ofMul h
  refine QuotientGroup.induction_on (Additive.toMul g) fun g => ?_
  change lowerCentralPieceBracket G m m
    (QuotientGroup.mk' (nextLowerCentralIn G m) g)
    (QuotientGroup.mk' (nextLowerCentralIn G m) g) = 1
  rw [lowerCentralPieceBracket_mk_mk]
  apply lowerCentralPieceAmbientHom_injective G (m + m + 1)
  rw [lowerCentralPieceAmbientHom_mk, map_one]
  change QuotientGroup.mk' (lowerCentralSeries G (m + m + 1 + 1))
      ⁅(g : G), (g : G)⁆ = 1
  rw [commutatorElement_self, map_one]

/-- Actual tensor-product induction extends graded antisymmetry to all
rationalized elements, not just pure representative tensors. -/
theorem rationalLowerCentralPieceBracket_swap (m n : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n) :
    rationalLowerCentralPieceReindex G (show n + m + 1 = m + n + 1 by omega)
      (rationalLowerCentralPieceBracket G n m y x) =
      -rationalLowerCentralPieceBracket G m n x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, neg_add]
    exact congrArg₂ (· + ·) hx₁ hx₂
  | tmul c g =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, LinearMap.add_apply, neg_add]
      exact congrArg₂ (· + ·) hy₁ hy₂
    | tmul d h =>
      rw [rationalLowerCentralPieceBracket_tmul_tmul,
        rationalLowerCentralPieceBracket_tmul_tmul,
        rationalLowerCentralPieceReindex_tmul,
        lowerCentralPieceBracketAdd_swap]
      simp only [TensorProduct.tmul_neg, mul_comm]

/-- Rational alternation follows from true antisymmetry and the actual
nonzero scalar two in the rational field. -/
theorem rationalLowerCentralPieceBracket_self (m : ℕ)
    (x : rationalLowerCentralPiece G m) :
    rationalLowerCentralPieceBracket G m m x x = 0 := by
  have hs := rationalLowerCentralPieceBracket_swap G m m x x
  change rationalLowerCentralPieceBracket G m m x x =
    -rationalLowerCentralPieceBracket G m m x x at hs
  have hadd : rationalLowerCentralPieceBracket G m m x x +
      rationalLowerCentralPieceBracket G m m x x = 0 := by
    calc
      _ = -rationalLowerCentralPieceBracket G m m x x +
          rationalLowerCentralPieceBracket G m m x x :=
        congrArg (fun z => z + rationalLowerCentralPieceBracket G m m x x) hs
      _ = 0 := neg_add_cancel _
  have htwo : (2 : ℚ) • rationalLowerCentralPieceBracket G m m x x = 0 := by
    simpa only [two_smul] using hadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end ChenRanks
