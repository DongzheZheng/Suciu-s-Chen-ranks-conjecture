import ChenRanks.GroupLowerCentralPieceAlternation

/-!
# Jacobi from the original Hall--Witt word identity

Triple commutators lie in their native joint lower-central term. Their
images are central modulo its actual next term. The Hall--Witt word
identity and the already constructed homomorphisms in both variables
therefore give the cyclic Jacobi identity on the original successive
quotients. This is independent of any augmentation injectivity or
group/holonomy comparison.
-/

noncomputable section

open scoped commutatorElement TensorProduct

namespace ChenRanks

variable (G : Type*) [Group G]

private theorem hallWitt_expanded_word {Q : Type*} [Group Q] (x y z : Q) :
    ⁅z, ⁅x, y⁆⁆ =
      x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y *
        ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
  simp only [commutatorElement_def]
  group

/-- Inverting both original quotient variables leaves the actual
commutator class unchanged. -/
theorem lowerCentralPieceBracket_inv_inv (m n : ℕ)
    (x : lowerCentralPiece G m) (y : lowerCentralPiece G n) :
    lowerCentralPieceBracket G m n x⁻¹ y⁻¹ =
      lowerCentralPieceBracket G m n x y := by
  rw [MonoidHom.map_inv₂, map_inv, inv_inv]

private theorem nested_second_inverse_pair_mod (m n p : ℕ)
    (x : lowerCentralSeries G m) (y : lowerCentralSeries G n)
    (z : lowerCentralSeries G p) :
    QuotientGroup.mk' (lowerCentralSeries G ((m + (n + p + 1) + 1) + 1))
      ⁅(x : G), ⁅(y : G)⁻¹, (z : G)⁻¹⁆⁆ =
    QuotientGroup.mk' (lowerCentralSeries G ((m + (n + p + 1) + 1) + 1))
      ⁅(x : G), ⁅(y : G), (z : G)⁆⁆ := by
  have h := lowerCentralPieceBracket_inv_inv G n p
    (QuotientGroup.mk' (nextLowerCentralIn G n) y)
    (QuotientGroup.mk' (nextLowerCentralIn G p) z)
  change lowerCentralPieceBracket G n p
      (QuotientGroup.mk' (nextLowerCentralIn G n) (y⁻¹))
      (QuotientGroup.mk' (nextLowerCentralIn G p) (z⁻¹)) =
    lowerCentralPieceBracket G n p
      (QuotientGroup.mk' (nextLowerCentralIn G n) y)
      (QuotientGroup.mk' (nextLowerCentralIn G p) z) at h
  have hmap := congrArg (fun w =>
    lowerCentralPieceAmbientHom G (m + (n + p + 1) + 1)
      (lowerCentralPieceBracket G m (n + p + 1)
        (QuotientGroup.mk' (nextLowerCentralIn G m) x) w)) h
  simpa only [lowerCentralPieceBracket_mk_mk,
    lowerCentralPieceAmbientHom_mk] using hmap

private theorem nested_second_inverse_pair_mod_reindex (m n p r : ℕ)
    (hr : (m + (n + p + 1) + 1) + 1 = r)
    (x y z : G) (hx : x ∈ lowerCentralSeries G m)
    (hy : y ∈ lowerCentralSeries G n) (hz : z ∈ lowerCentralSeries G p) :
    QuotientGroup.mk' (lowerCentralSeries G r) ⁅x, ⁅y⁻¹, z⁻¹⁆⁆ =
      QuotientGroup.mk' (lowerCentralSeries G r) ⁅x, ⁅y, z⁆⁆ := by
  subst r
  exact nested_second_inverse_pair_mod G m n p ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩

private theorem nested_first_second_inverse_mod (m n p : ℕ)
    (x : lowerCentralSeries G m) (y : lowerCentralSeries G n)
    (z : lowerCentralSeries G p) :
    QuotientGroup.mk' (lowerCentralSeries G ((m + (n + p + 1) + 1) + 1))
      ⁅(x : G)⁻¹, ⁅(y : G)⁻¹, (z : G)⁆⁆ =
    QuotientGroup.mk' (lowerCentralSeries G ((m + (n + p + 1) + 1) + 1))
      ⁅(x : G), ⁅(y : G), (z : G)⁆⁆ := by
  have h :
      lowerCentralPieceBracket G m (n + p + 1)
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)⁻¹
        (lowerCentralPieceBracket G n p
          (QuotientGroup.mk' (nextLowerCentralIn G n) y)⁻¹
          (QuotientGroup.mk' (nextLowerCentralIn G p) z)) =
      lowerCentralPieceBracket G m (n + p + 1)
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)
        (lowerCentralPieceBracket G n p
          (QuotientGroup.mk' (nextLowerCentralIn G n) y)
          (QuotientGroup.mk' (nextLowerCentralIn G p) z)) := by
    rw [MonoidHom.map_inv₂, MonoidHom.map_inv₂, map_inv, inv_inv]
  change lowerCentralPieceBracket G m (n + p + 1)
      (QuotientGroup.mk' (nextLowerCentralIn G m) (x⁻¹))
      (lowerCentralPieceBracket G n p
        (QuotientGroup.mk' (nextLowerCentralIn G n) (y⁻¹))
        (QuotientGroup.mk' (nextLowerCentralIn G p) z)) =
    lowerCentralPieceBracket G m (n + p + 1)
      (QuotientGroup.mk' (nextLowerCentralIn G m) x)
      (lowerCentralPieceBracket G n p
        (QuotientGroup.mk' (nextLowerCentralIn G n) y)
        (QuotientGroup.mk' (nextLowerCentralIn G p) z)) at h
  have hmap := congrArg
    (lowerCentralPieceAmbientHom G (m + (n + p + 1) + 1)) h
  simpa only [lowerCentralPieceBracket_mk_mk,
    lowerCentralPieceAmbientHom_mk] using hmap

private theorem nested_first_second_inverse_mod_reindex (m n p r : ℕ)
    (hr : (m + (n + p + 1) + 1) + 1 = r)
    (x y z : G) (hx : x ∈ lowerCentralSeries G m)
    (hy : y ∈ lowerCentralSeries G n) (hz : z ∈ lowerCentralSeries G p) :
    QuotientGroup.mk' (lowerCentralSeries G r) ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ =
      QuotientGroup.mk' (lowerCentralSeries G r) ⁅x, ⁅y, z⁆⁆ := by
  subst r
  exact nested_first_second_inverse_mod G m n p ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩

private theorem jacobi_of_inverse_word_central {Q : Type*} [Group Q]
    (x y z : Q)
    (hB : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ = ⁅y, ⁅z, x⁆⁆)
    (hC : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ = ⁅x, ⁅y, z⁆⁆)
    (hBz : Commute ⁅y, ⁅z, x⁆⁆ z) (hBx : Commute ⁅y, ⁅z, x⁆⁆ x)
    (hCx : Commute ⁅x, ⁅y, z⁆⁆ x) (hCy : Commute ⁅x, ⁅y, z⁆⁆ y) :
    ⁅x, ⁅y, z⁆⁆ * ⁅y, ⁅z, x⁆⁆ * ⁅z, ⁅x, y⁆⁆ = 1 := by
  have hword := hallWitt_expanded_word x y z
  rw [hB, hC] at hword
  have hconjB : z * ⁅y, ⁅z, x⁆⁆⁻¹ * z⁻¹ = ⁅y, ⁅z, x⁆⁆⁻¹ := by
    rw [hBz.inv_left.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconjC : y * ⁅x, ⁅y, z⁆⁆⁻¹ * y⁻¹ = ⁅x, ⁅y, z⁆⁆⁻¹ := by
    rw [hCy.inv_left.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconjX : x * (⁅y, ⁅z, x⁆⁆⁻¹ * ⁅x, ⁅y, z⁆⁆⁻¹) * x⁻¹ =
      ⁅y, ⁅z, x⁆⁆⁻¹ * ⁅x, ⁅y, z⁆⁆⁻¹ := by
    have hc := hBx.inv_left.mul_left hCx.inv_left
    rw [hc.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hzword : ⁅z, ⁅x, y⁆⁆ = ⁅y, ⁅z, x⁆⁆⁻¹ * ⁅x, ⁅y, z⁆⁆⁻¹ := by
    calc
      _ = x * (z * ⁅y, ⁅z, x⁆⁆⁻¹ * z⁻¹) *
          (y * ⁅x, ⁅y, z⁆⁆⁻¹ * y⁻¹) * x⁻¹ := by
        simpa only [mul_assoc] using hword
      _ = x * (⁅y, ⁅z, x⁆⁆⁻¹ * ⁅x, ⁅y, z⁆⁆⁻¹) * x⁻¹ := by
        rw [hconjB, hconjC]
        simp only [mul_assoc]
      _ = _ := hconjX
  rw [hzword]
  group

/-- The literal original quotient by the next total lower-central term
satisfies cyclic Jacobi on actual representative commutators. -/
theorem lowerCentral_nested_commutator_jacobi_mod (m n p : ℕ)
    (x y z : G) (hx : x ∈ lowerCentralSeries G m)
    (hy : y ∈ lowerCentralSeries G n) (hz : z ∈ lowerCentralSeries G p) :
    QuotientGroup.mk' (lowerCentralSeries G (m + n + p + 3)) ⁅x, ⁅y, z⁆⁆ *
      QuotientGroup.mk' (lowerCentralSeries G (m + n + p + 3)) ⁅y, ⁅z, x⁆⁆ *
      QuotientGroup.mk' (lowerCentralSeries G (m + n + p + 3)) ⁅z, ⁅x, y⁆⁆ =
        1 := by
  let q : G →* G ⧸ lowerCentralSeries G (m + n + p + 3) :=
    QuotientGroup.mk' _
  have hB : q ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ = q ⁅y, ⁅z, x⁆⁆ := by
    exact nested_second_inverse_pair_mod_reindex G n p m (m + n + p + 3)
      (by omega) y z x hy hz hx
  have hC : q ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ = q ⁅x, ⁅y, z⁆⁆ := by
    exact nested_first_second_inverse_mod_reindex G m n p (m + n + p + 3)
      (by omega) x y z hx hy hz
  have hBm : ⁅y, ⁅z, x⁆⁆ ∈ lowerCentralSeries G (m + n + p + 2) := by
    simpa only [show n + (p + m + 1) + 1 = m + n + p + 2 by omega] using
      group_commutator_mem_lowerCentralSeries (G := G) n (p + m + 1) y ⁅z, x⁆ hy
        (group_commutator_mem_lowerCentralSeries (G := G) p m z x hz hx)
  have hCm : ⁅x, ⁅y, z⁆⁆ ∈ lowerCentralSeries G (m + n + p + 2) := by
    simpa only [show m + (n + p + 1) + 1 = m + n + p + 2 by omega] using
      group_commutator_mem_lowerCentralSeries (G := G) m (n + p + 1) x ⁅y, z⁆ hx
        (group_commutator_mem_lowerCentralSeries (G := G) n p y z hy hz)
  have hBz : Commute (q ⁅y, ⁅z, x⁆⁆) (q z) :=
    lowerCentral_ambient_image_commute G (m + n + p + 2) _ hBm z
  have hBx : Commute (q ⁅y, ⁅z, x⁆⁆) (q x) :=
    lowerCentral_ambient_image_commute G (m + n + p + 2) _ hBm x
  have hCx : Commute (q ⁅x, ⁅y, z⁆⁆) (q x) :=
    lowerCentral_ambient_image_commute G (m + n + p + 2) _ hCm x
  have hCy : Commute (q ⁅x, ⁅y, z⁆⁆) (q y) :=
    lowerCentral_ambient_image_commute G (m + n + p + 2) _ hCm y
  have hB' : ⁅q y, ⁅(q z)⁻¹, (q x)⁻¹⁆⁆ = ⁅q y, ⁅q z, q x⁆⁆ := by
    simpa only [map_commutatorElement, map_inv] using hB
  have hC' : ⁅(q x)⁻¹, ⁅(q y)⁻¹, q z⁆⁆ = ⁅q x, ⁅q y, q z⁆⁆ := by
    simpa only [map_commutatorElement, map_inv] using hC
  have hBz' : Commute ⁅q y, ⁅q z, q x⁆⁆ (q z) := by
    simpa only [map_commutatorElement] using hBz
  have hBx' : Commute ⁅q y, ⁅q z, q x⁆⁆ (q x) := by
    simpa only [map_commutatorElement] using hBx
  have hCx' : Commute ⁅q x, ⁅q y, q z⁆⁆ (q x) := by
    simpa only [map_commutatorElement] using hCx
  have hCy' : Commute ⁅q x, ⁅q y, q z⁆⁆ (q y) := by
    simpa only [map_commutatorElement] using hCy
  simpa only [map_commutatorElement] using
    jacobi_of_inverse_word_central (q x) (q y) (q z) hB' hC' hBz' hBx' hCx' hCy'

/-- Reindex an actual nested quotient bracket to its actual total term.
The equality only compares native natural-number indices. -/
def lowerCentralPieceJacobiTerm (m n p r : ℕ)
    (h : m + (n + p + 1) + 1 = r)
    (x : lowerCentralPiece G m) (y : lowerCentralPiece G n)
    (z : lowerCentralPiece G p) : lowerCentralPiece G r :=
  lowerCentralPieceReindex G h
    (lowerCentralPieceBracket G m (n + p + 1) x
      (lowerCentralPieceBracket G n p y z))

theorem lowerCentralPieceJacobiTerm_mk_ambient (m n p r : ℕ)
    (h : m + (n + p + 1) + 1 = r)
    (x : lowerCentralSeries G m) (y : lowerCentralSeries G n)
    (z : lowerCentralSeries G p) :
    lowerCentralPieceAmbientHom G r
      (lowerCentralPieceJacobiTerm G m n p r h
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)
        (QuotientGroup.mk' (nextLowerCentralIn G n) y)
        (QuotientGroup.mk' (nextLowerCentralIn G p) z)) =
      QuotientGroup.mk' (lowerCentralSeries G (r + 1))
        ⁅(x : G), ⁅(y : G), (z : G)⁆⁆ := by
  unfold lowerCentralPieceJacobiTerm
  rw [lowerCentralPieceBracket_mk_mk, lowerCentralPieceBracket_mk_mk,
    lowerCentralPieceReindex_mk_ambient]

/-- Jacobi is a theorem on the original quotient classes, proved by
injectivity of their actual maps to the original ambient quotient. -/
theorem lowerCentralPieceBracket_jacobi (m n p : ℕ)
    (x : lowerCentralPiece G m) (y : lowerCentralPiece G n)
    (z : lowerCentralPiece G p) :
    lowerCentralPieceJacobiTerm G m n p (m + n + p + 2) (by omega) x y z *
      lowerCentralPieceJacobiTerm G n p m (m + n + p + 2) (by omega) y z x *
      lowerCentralPieceJacobiTerm G p m n (m + n + p + 2) (by omega) z x y =
        1 := by
  refine QuotientGroup.induction_on x fun x => ?_
  refine QuotientGroup.induction_on y fun y => ?_
  refine QuotientGroup.induction_on z fun z => ?_
  change lowerCentralPieceJacobiTerm G m n p (m + n + p + 2) _
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)
        (QuotientGroup.mk' (nextLowerCentralIn G n) y)
        (QuotientGroup.mk' (nextLowerCentralIn G p) z) *
      lowerCentralPieceJacobiTerm G n p m (m + n + p + 2) _
        (QuotientGroup.mk' (nextLowerCentralIn G n) y)
        (QuotientGroup.mk' (nextLowerCentralIn G p) z)
        (QuotientGroup.mk' (nextLowerCentralIn G m) x) *
      lowerCentralPieceJacobiTerm G p m n (m + n + p + 2) _
        (QuotientGroup.mk' (nextLowerCentralIn G p) z)
        (QuotientGroup.mk' (nextLowerCentralIn G m) x)
        (QuotientGroup.mk' (nextLowerCentralIn G n) y) = 1
  apply lowerCentralPieceAmbientHom_injective G (m + n + p + 2)
  rw [map_mul, map_mul, lowerCentralPieceJacobiTerm_mk_ambient,
    lowerCentralPieceJacobiTerm_mk_ambient,
    lowerCentralPieceJacobiTerm_mk_ambient, map_one]
  exact lowerCentral_nested_commutator_jacobi_mod G m n p
    (x : G) (y : G) (z : G) x.property y.property z.property

/-- The same actual nested quotient bracket in its native additive form. -/
def lowerCentralPieceIntJacobiTerm (m n p r : ℕ)
    (h : m + (n + p + 1) + 1 = r)
    (x : Additive (lowerCentralPiece G m))
    (y : Additive (lowerCentralPiece G n))
    (z : Additive (lowerCentralPiece G p)) : Additive (lowerCentralPiece G r) :=
  lowerCentralPieceIntReindex G h
    (lowerCentralPieceBracketAdd G m (n + p + 1) x
      (lowerCentralPieceBracketAdd G n p y z))

@[simp] theorem lowerCentralPieceIntJacobiTerm_ofMul (m n p r : ℕ)
    (h : m + (n + p + 1) + 1 = r)
    (x : lowerCentralPiece G m) (y : lowerCentralPiece G n)
    (z : lowerCentralPiece G p) :
    lowerCentralPieceIntJacobiTerm G m n p r h
      (Additive.ofMul x) (Additive.ofMul y) (Additive.ofMul z) =
      Additive.ofMul (lowerCentralPieceJacobiTerm G m n p r h x y z) := by
  change lowerCentralPieceIntReindex G h
      (Additive.ofMul (lowerCentralPieceBracket G m (n + p + 1) x
        (lowerCentralPieceBracket G n p y z))) = _
  exact lowerCentralPieceIntReindex_ofMul G h _

/-- Literal integral Jacobi, before any scalar extension. -/
theorem lowerCentralPieceBracketAdd_jacobi (m n p : ℕ)
    (x : Additive (lowerCentralPiece G m))
    (y : Additive (lowerCentralPiece G n))
    (z : Additive (lowerCentralPiece G p)) :
    lowerCentralPieceIntJacobiTerm G m n p (m + n + p + 2) (by omega) x y z +
      lowerCentralPieceIntJacobiTerm G n p m (m + n + p + 2) (by omega) y z x +
      lowerCentralPieceIntJacobiTerm G p m n (m + n + p + 2) (by omega) z x y =
        0 := by
  rw [show x = Additive.ofMul (Additive.toMul x) from rfl,
    show y = Additive.ofMul (Additive.toMul y) from rfl,
    show z = Additive.ofMul (Additive.toMul z) from rfl,
    lowerCentralPieceIntJacobiTerm_ofMul, lowerCentralPieceIntJacobiTerm_ofMul,
    lowerCentralPieceIntJacobiTerm_ofMul]
  exact congrArg Additive.ofMul (lowerCentralPieceBracket_jacobi G m n p
    (Additive.toMul x) (Additive.toMul y) (Additive.toMul z))

/-- Genuine rational nested brackets, reindexed only by the equality of
their original total native lower-central indices. -/
def rationalLowerCentralPieceJacobiTerm (m n p r : ℕ)
    (h : m + (n + p + 1) + 1 = r)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) : rationalLowerCentralPiece G r :=
  rationalLowerCentralPieceReindex G h
    (rationalLowerCentralPieceBracket G m (n + p + 1) x
      (rationalLowerCentralPieceBracket G n p y z))

theorem rationalLowerCentralPieceJacobiTerm_tmul (m n p r : ℕ)
    (h : m + (n + p + 1) + 1 = r) (c d e : ℚ)
    (x : Additive (lowerCentralPiece G m))
    (y : Additive (lowerCentralPiece G n))
    (z : Additive (lowerCentralPiece G p)) :
    rationalLowerCentralPieceJacobiTerm G m n p r h
      (c ⊗ₜ[ℤ] x) (d ⊗ₜ[ℤ] y) (e ⊗ₜ[ℤ] z) =
      (c * (d * e)) ⊗ₜ[ℤ]
        lowerCentralPieceIntJacobiTerm G m n p r h x y z := by
  unfold rationalLowerCentralPieceJacobiTerm
  rw [rationalLowerCentralPieceBracket_tmul_tmul,
    rationalLowerCentralPieceBracket_tmul_tmul,
    rationalLowerCentralPieceReindex_tmul]
  rfl

private def rationalJacobiSum (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) : rationalLowerCentralPiece G (m + n + p + 2) :=
  rationalLowerCentralPieceJacobiTerm G m n p (m + n + p + 2) (by omega) x y z +
    rationalLowerCentralPieceJacobiTerm G n p m (m + n + p + 2) (by omega) y z x +
    rationalLowerCentralPieceJacobiTerm G p m n (m + n + p + 2) (by omega) z x y

private theorem rationalJacobiSum_zero_left (m n p : ℕ)
    (y : rationalLowerCentralPiece G n) (z : rationalLowerCentralPiece G p) :
    rationalJacobiSum G m n p 0 y z = 0 := by
  simp only [rationalJacobiSum, rationalLowerCentralPieceJacobiTerm,
    map_zero, LinearMap.zero_apply, add_zero]

private theorem rationalJacobiSum_zero_middle (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (z : rationalLowerCentralPiece G p) :
    rationalJacobiSum G m n p x 0 z = 0 := by
  simp only [rationalJacobiSum, rationalLowerCentralPieceJacobiTerm,
    map_zero, LinearMap.zero_apply, add_zero]

private theorem rationalJacobiSum_zero_right (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n) :
    rationalJacobiSum G m n p x y 0 = 0 := by
  simp only [rationalJacobiSum, rationalLowerCentralPieceJacobiTerm,
    map_zero, LinearMap.zero_apply, add_zero]

private theorem rationalJacobiSum_add_left (m n p : ℕ)
    (x₁ x₂ : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) :
    rationalJacobiSum G m n p (x₁ + x₂) y z =
      rationalJacobiSum G m n p x₁ y z + rationalJacobiSum G m n p x₂ y z := by
  simp only [rationalJacobiSum, rationalLowerCentralPieceJacobiTerm,
    map_add, LinearMap.add_apply]
  abel

private theorem rationalJacobiSum_add_middle (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (y₁ y₂ : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) :
    rationalJacobiSum G m n p x (y₁ + y₂) z =
      rationalJacobiSum G m n p x y₁ z + rationalJacobiSum G m n p x y₂ z := by
  simp only [rationalJacobiSum, rationalLowerCentralPieceJacobiTerm,
    map_add, LinearMap.add_apply]
  abel

private theorem rationalJacobiSum_add_right (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z₁ z₂ : rationalLowerCentralPiece G p) :
    rationalJacobiSum G m n p x y (z₁ + z₂) =
      rationalJacobiSum G m n p x y z₁ + rationalJacobiSum G m n p x y z₂ := by
  simp only [rationalJacobiSum, rationalLowerCentralPieceJacobiTerm,
    map_add, LinearMap.add_apply]
  abel

private theorem rationalJacobiSum_tmul (m n p : ℕ) (c d e : ℚ)
    (x : Additive (lowerCentralPiece G m))
    (y : Additive (lowerCentralPiece G n))
    (z : Additive (lowerCentralPiece G p)) :
    rationalJacobiSum G m n p (c ⊗ₜ[ℤ] x) (d ⊗ₜ[ℤ] y) (e ⊗ₜ[ℤ] z) = 0 := by
  unfold rationalJacobiSum
  rw [rationalLowerCentralPieceJacobiTerm_tmul,
    rationalLowerCentralPieceJacobiTerm_tmul,
    rationalLowerCentralPieceJacobiTerm_tmul]
  rw [show d * (e * c) = c * (d * e) by ring,
    show e * (c * d) = c * (d * e) by ring,
    ← TensorProduct.tmul_add, ← TensorProduct.tmul_add,
    lowerCentralPieceBracketAdd_jacobi, TensorProduct.tmul_zero]

/-- Jacobi holds for every element of the actual rationalizations,
by genuine tensor induction in all three variables. -/
theorem rationalLowerCentralPieceBracket_jacobi (m n p : ℕ)
    (x : rationalLowerCentralPiece G m) (y : rationalLowerCentralPiece G n)
    (z : rationalLowerCentralPiece G p) :
    rationalLowerCentralPieceJacobiTerm G m n p (m + n + p + 2) (by omega) x y z +
      rationalLowerCentralPieceJacobiTerm G n p m (m + n + p + 2) (by omega) y z x +
      rationalLowerCentralPieceJacobiTerm G p m n (m + n + p + 2) (by omega) z x y =
        0 := by
  change rationalJacobiSum G m n p x y z = 0
  induction x using TensorProduct.induction_on with
  | zero => exact rationalJacobiSum_zero_left G m n p y z
  | add x₁ x₂ ih₁ ih₂ =>
    rw [rationalJacobiSum_add_left, ih₁, ih₂, add_zero]
  | tmul c x =>
    induction y using TensorProduct.induction_on with
    | zero => exact rationalJacobiSum_zero_middle G m n p (c ⊗ₜ[ℤ] x) z
    | add y₁ y₂ ih₁ ih₂ =>
      rw [rationalJacobiSum_add_middle, ih₁, ih₂, add_zero]
    | tmul d y =>
      induction z using TensorProduct.induction_on with
      | zero => exact rationalJacobiSum_zero_right G m n p (c ⊗ₜ[ℤ] x) (d ⊗ₜ[ℤ] y)
      | add z₁ z₂ ih₁ ih₂ =>
        rw [rationalJacobiSum_add_right, ih₁, ih₂, add_zero]
      | tmul e z => exact rationalJacobiSum_tmul G m n p c d e x y z

end ChenRanks
