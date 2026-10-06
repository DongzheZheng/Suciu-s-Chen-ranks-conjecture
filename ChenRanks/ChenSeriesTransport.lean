import ChenRanks.ChenAbelianFactor

/-!
# Genuine lower-central quotient transport

An actual group equivalence carries the actual lower central series to
the actual lower central series. Restriction and quotient functoriality
then give equivalences of the genuine successive quotients. Together
with the product-series computation, this is the group-theoretic part
of the manuscript's central-arrangement reduction, before topological
deconing is identified.
-/

noncomputable section

namespace ChenRanks

variable {G H : Type*} [Group G] [Group H]

/-- The genuine lower central series is preserved by an actual group
equivalence, by induction using the actual commutator map. -/
theorem lowerCentralSeries_map_equiv (e : G ≃* H) (n : ℕ) :
    (lowerCentralSeries G n).map e.toMonoidHom = lowerCentralSeries H n := by
  induction n with
  | zero =>
    rw [lowerCentralSeries_zero, lowerCentralSeries_zero,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  | succ n ih =>
    change Subgroup.map e.toMonoidHom
        ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆ =
      ⁅lowerCentralSeries H n, (⊤ : Subgroup H)⁆
    rw [Subgroup.map_commutator, ih,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- Restriction of the given group equivalence to the actual series
subgroups, retaining their original subgroup types. -/
def lowerCentralSeriesEquiv (e : G ≃* H) (n : ℕ) :
    lowerCentralSeries G n ≃* lowerCentralSeries H n :=
  (e.subgroupMap (lowerCentralSeries G n)).trans
    (MulEquiv.subgroupCongr (lowerCentralSeries_map_equiv e n))

/-- The actual next subgroup inside the numerator is carried to its
actual counterpart, so quotient transport uses no supplied kernel identity. -/
theorem nextLowerCentralIn_map_equiv (e : G ≃* H) (n : ℕ) :
    (nextLowerCentralIn G n).map (lowerCentralSeriesEquiv e n).toMonoidHom =
      nextLowerCentralIn H n := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change e (x : G) ∈ lowerCentralSeries H (n + 1)
    rw [← lowerCentralSeries_map_equiv e (n + 1)]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  · intro y hy
    obtain ⟨x, rfl⟩ := (lowerCentralSeriesEquiv e n).surjective y
    refine ⟨x, ?_, rfl⟩
    change (x : G) ∈ lowerCentralSeries G (n + 1)
    change e (x : G) ∈ lowerCentralSeries H (n + 1) at hy
    rw [← lowerCentralSeries_map_equiv e (n + 1)] at hy
    obtain ⟨z, hz, hzx⟩ := hy
    have heq : z = (x : G) := e.injective hzx
    simpa only [heq] using hz

/-- Genuine successive quotient equivalence induced by the original
group equivalence. -/
def lowerCentralPieceEquiv (e : G ≃* H) (n : ℕ) :
    lowerCentralPiece G n ≃* lowerCentralPiece H n :=
  QuotientGroup.congr (nextLowerCentralIn G n) (nextLowerCentralIn H n)
    (lowerCentralSeriesEquiv e n)
    (nextLowerCentralIn_map_equiv e n)

variable (G) (A : Type*) [CommGroup A]

/-- The actual product-series membership formula, stated on an ambient
element so later use does not rewrite the type of a subgroup element. -/
theorem mem_lowerCentralSeries_product (n : ℕ) (x : G × A) :
    x ∈ lowerCentralSeries (G × A) n ↔
      x.1 ∈ lowerCentralSeries G n ∧ x.2 ∈ lowerCentralSeries A n := by
  rw [lowerCentralSeries_prod]
  rfl

/-- Projection removes the abelian factor from each actual positive
lower-central subgroup; its inverse is the original inclusion at one. -/
def lowerCentralProductSuccEquiv (n : ℕ) :
    lowerCentralSeries (G × A) (n + 1) ≃* lowerCentralSeries G (n + 1) where
  toFun x := ⟨x.val.1, by
    exact ((mem_lowerCentralSeries_product G A (n + 1) x.val).mp x.property).1⟩
  invFun x := ⟨(x.val, 1), by
    rw [lowerCentralSeries_prod]
    exact ⟨x.property, (lowerCentralSeries A (n + 1)).one_mem⟩⟩
  left_inv x := by
    apply Subtype.ext
    change (x.val.1, (1 : A)) = x.val
    refine Prod.ext rfl ?_
    have hx := (mem_lowerCentralSeries_product G A (n + 1) x.val).mp x.property
    have ha := hx.2
    rw [abelian_lowerCentralSeries_succ A n, Subgroup.mem_bot] at ha
    exact ha.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The projection also carries the genuine next subgroup inside the
positive lower-central term to the genuine next subgroup in the factor. -/
theorem nextLowerCentralIn_map_product_succ (n : ℕ) :
    (nextLowerCentralIn (G × A) (n + 1)).map
        (lowerCentralProductSuccEquiv G A n).toMonoidHom =
      nextLowerCentralIn G (n + 1) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change x.val.1 ∈ lowerCentralSeries G (n + 1 + 1)
    change x.val ∈ lowerCentralSeries (G × A) (n + 1 + 1) at hx
    rw [lowerCentralSeries_prod] at hx
    exact hx.1
  · intro y hy
    let x := (lowerCentralProductSuccEquiv G A n).symm y
    refine ⟨x, ?_, (lowerCentralProductSuccEquiv G A n).apply_symm_apply y⟩
    change (y.val, (1 : A)) ∈ lowerCentralSeries (G × A) (n + 1 + 1)
    rw [lowerCentralSeries_prod]
    exact ⟨hy, (lowerCentralSeries A (n + 1 + 1)).one_mem⟩

/-- The abelian factor contributes nothing to the actual successive
lower-central quotient in ordinary group degree at least two. -/
def lowerCentralProductPieceSuccEquiv (n : ℕ) :
    lowerCentralPiece (G × A) (n + 1) ≃* lowerCentralPiece G (n + 1) :=
  QuotientGroup.congr (nextLowerCentralIn (G × A) (n + 1))
    (nextLowerCentralIn G (n + 1)) (lowerCentralProductSuccEquiv G A n)
    (nextLowerCentralIn_map_product_succ G A n)

/-- The actual Chen numerator and denominator for an abelian direct
factor give the same genuine quotient in every Chen degree at least two.
The group equivalences come from the actual quotient and projection maps. -/
def metabelianLowerCentralProductPieceSuccEquiv (n : ℕ) :
    lowerCentralPiece (metabelianQuotient (G × A)) (n + 1) ≃*
      lowerCentralPiece (metabelianQuotient G) (n + 1) :=
  (lowerCentralPieceEquiv (metabelianProductEquiv G A) (n + 1)).trans
    (lowerCentralProductPieceSuccEquiv (metabelianQuotient G) A n)

end ChenRanks
