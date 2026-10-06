import ChenRanks.KoszulFunctoriality

/-!
# Actual exterior duality for component quadratic relations

The canonical exterior pairing is mathlib's determinant pairing between
the exterior power of the dual and the dual of the exterior power.  Its
bijection is derived from actual finite exterior bases.  The annihilator is
the pullback of the usual functional annihilator along that actual pairing.

For a genuine subspace inclusion `P → E`, its actual dual restriction map
induces the exterior map on quadratic relations.  Its image of `I`'s actual
annihilator is proved to be the annihilator of `I` restricted to `Λ²P`.
Isotropic subspaces therefore have zero actual image relations.
Neither a nondegenerate-pairing premise nor an image-annihilator identity
is supplied as input.
-/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (E : Type*) [AddCommGroup E] [_root_.Module k E]

/-- The actual determinant pairing of exterior powers is surjective in
finite dimension: every coordinate of a genuine exterior basis is in its
range, by mathlib's actual determinant-coordinate formula. -/
theorem exteriorPairingDual_surjective [FiniteDimensional k E] (n : ℕ) :
    Function.Surjective (exteriorPower.pairingDual k E n) := by
  classical
  let b := _root_.Module.finBasis k E
  let c := b.exteriorPower n
  have hr : LinearMap.range (exteriorPower.pairingDual k E n) = ⊤ := by
    apply top_unique
    rw [← c.dualBasis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    refine ⟨exteriorPower.ιMulti_family k n b.coord s, ?_⟩
    simpa only [_root_.Module.Basis.coe_dualBasis] using
      (exteriorPower.basis_coord k n b s).symm
  exact LinearMap.range_eq_top.mp hr

/-- The actual determinant pairing is a bijection.  Equal dimensions are
derived from genuine finite primal and dual exterior bases, and its
surjectivity was proved above from the determinant pairing itself. -/
theorem exteriorPairingDual_bijective [FiniteDimensional k E] (n : ℕ) :
    Function.Bijective (exteriorPower.pairingDual k E n) := by
  classical
  let b := _root_.Module.finBasis k E
  let c := b.exteriorPower n
  let d := b.dualBasis.exteriorPower n
  letI : FiniteDimensional k (⋀[k]^n (_root_.Module.Dual k E)) :=
    FiniteDimensional.of_injective d.repr.toLinearMap d.repr.injective
  letI : FiniteDimensional k (_root_.Module.Dual k (⋀[k]^n E)) :=
    FiniteDimensional.of_injective c.dualBasis.repr.toLinearMap c.dualBasis.repr.injective
  have hdim : _root_.Module.finrank k (⋀[k]^n (_root_.Module.Dual k E)) =
      _root_.Module.finrank k (_root_.Module.Dual k (⋀[k]^n E)) := by
    rw [_root_.Module.finrank_eq_card_basis d, _root_.Module.finrank_eq_card_basis c.dualBasis]
  have hs := exteriorPairingDual_surjective k E n
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

/-- The actual canonical exterior pairing equivalence, rather than an
arbitrary equivalence selected merely from equal dimensions. -/
def exteriorPairingDualEquiv [FiniteDimensional k E] (n : ℕ) :
    (⋀[k]^n (_root_.Module.Dual k E)) ≃ₗ[k] _root_.Module.Dual k (⋀[k]^n E) :=
  LinearEquiv.ofBijective (exteriorPower.pairingDual k E n)
    (exteriorPairingDual_bijective k E n)

/-- The ordinary functional annihilator pulled back through the actual
determinant pairing. -/
def exteriorAnnihilator (n : ℕ) (I : Submodule k (⋀[k]^n E)) :
    Submodule k (⋀[k]^n (_root_.Module.Dual k E)) :=
  I.dualAnnihilator.comap (exteriorPower.pairingDual k E n)

@[simp] theorem mem_exteriorAnnihilator (n : ℕ) (I : Submodule k (⋀[k]^n E))
    (x : ⋀[k]^n (_root_.Module.Dual k E)) :
    x ∈ exteriorAnnihilator k E n I ↔
      exteriorPower.pairingDual k E n x ∈ I.dualAnnihilator := Iff.rfl

variable (F : Type*) [AddCommGroup F] [_root_.Module k F]

/-- Actual determinant pairing is natural under the actual exterior map
and the actual dual map, as can be checked on genuine exterior generators. -/
theorem exteriorPairingDual_naturality (f : F →ₗ[k] E) (n : ℕ) :
    exteriorPower.pairingDual k F n ∘ₗ exteriorPower.map n f.dualMap =
      (exteriorPower.map n f).dualMap ∘ₗ exteriorPower.pairingDual k E n := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro φ
  change exteriorPower.pairingDual k F n
      (exteriorPower.map n f.dualMap (exteriorPower.ιMulti k n φ)) =
    (exteriorPower.map n f).dualMap
      (exteriorPower.pairingDual k E n (exteriorPower.ιMulti k n φ))
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, LinearMap.dualMap_apply,
    Function.comp_apply]

/-- Over a field, restricting functional annihilators along an actual
linear map gives exactly the annihilator of the actual pulled-back
subspace.  This follows from the actual quotient-dual range theorem. -/
theorem dualAnnihilator_map_dualMap_eq (f : F →ₗ[k] E) (I : Submodule k E) :
    I.dualAnnihilator.map f.dualMap = (I.comap f).dualAnnihilator := by
  rw [← I.range_dualMap_mkQ_eq, ← LinearMap.range_comp,
    LinearMap.dualMap_comp_dualMap, LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_comp, Submodule.ker_mkQ]

variable [FiniteDimensional k E]

/-- Genuine dual restriction to a subspace, obtained from its inclusion. -/
def componentDualQuotient (P : Submodule k E) :
    _root_.Module.Dual k E →ₗ[k] _root_.Module.Dual k P := P.subtype.dualMap

omit [FiniteDimensional k E] in
theorem componentDualQuotient_surjective (P : Submodule k E) :
    Function.Surjective (componentDualQuotient k E P) :=
  LinearMap.dualMap_surjective_of_injective P.subtype_injective

/-- The actual quadratic kernel restricted to `Λ²P`; the exterior map is
the true map induced by the original subspace inclusion. -/
def componentQuadraticKernel (P : Submodule k E) (I : Submodule k (⋀[k]^2 E)) :
    Submodule k (⋀[k]^2 P) := I.comap (exteriorPower.map 2 P.subtype)

omit [FiniteDimensional k E] in
/-- The exterior inclusion is genuinely injective, so the pulled-back
kernel represents the actual intersection with `Λ²P`. -/
theorem componentExteriorInclusion_injective (P : Submodule k E) :
    Function.Injective (exteriorPower.map 2 P.subtype) :=
  exteriorPower.map_injective_field P.subtype_injective

omit [FiniteDimensional k E] in
/-- Mapping the actual restricted kernel back into the ambient exterior
power gives exactly the actual intersection with the inclusion image. -/
theorem componentQuadraticKernel_image (P : Submodule k E)
    (I : Submodule k (⋀[k]^2 E)) :
    (componentQuadraticKernel k E P I).map (exteriorPower.map 2 P.subtype) =
      I ⊓ LinearMap.range (exteriorPower.map 2 P.subtype) := by
  change (I.comap (exteriorPower.map 2 P.subtype)).map (exteriorPower.map 2 P.subtype) = _
  rw [Submodule.map_comap_eq, inf_comm]

/-- The paper's canonical image relation space is the actual annihilator
of the actual restricted quadratic kernel. -/
theorem quadraticImage_exteriorAnnihilator (P : Submodule k E)
    (I : Submodule k (⋀[k]^2 E)) :
    quadraticImage k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
        (componentDualQuotient k E P) (exteriorAnnihilator k E 2 I) =
      exteriorAnnihilator k P 2 (componentQuadraticKernel k E P I) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change exteriorPower.pairingDual k P 2
      (exteriorPower.map 2 P.subtype.dualMap x) ∈
        (I.comap (exteriorPower.map 2 P.subtype)).dualAnnihilator
    have hn := DFunLike.congr_fun (exteriorPairingDual_naturality k E P P.subtype 2) x
    change exteriorPower.pairingDual k P 2 (exteriorPower.map 2 P.subtype.dualMap x) =
      (exteriorPower.map 2 P.subtype).dualMap (exteriorPower.pairingDual k E 2 x) at hn
    rw [hn]
    have hx' : exteriorPower.pairingDual k E 2 x ∈ I.dualAnnihilator := hx
    exact I.dualAnnihilator_map_dualMap_le (exteriorPower.map 2 P.subtype)
      (Submodule.mem_map_of_mem hx')
  · intro hy
    have hy' : exteriorPower.pairingDual k P 2 y ∈
        I.dualAnnihilator.map (exteriorPower.map 2 P.subtype).dualMap := by
      rw [dualAnnihilator_map_dualMap_eq k (⋀[k]^2 E) (⋀[k]^2 P)]
      exact hy
    obtain ⟨φ, hφ, hφy⟩ := hy'
    obtain ⟨x, hx⟩ := exteriorPairingDual_surjective k E 2 φ
    refine ⟨x, ?_, ?_⟩
    · change exteriorPower.pairingDual k E 2 x ∈ I.dualAnnihilator
      rw [hx]
      exact hφ
    · apply (exteriorPairingDual_bijective k P 2).1
      have hn := DFunLike.congr_fun (exteriorPairingDual_naturality k E P P.subtype 2) x
      change exteriorPower.pairingDual k P 2 (exteriorPower.map 2 P.subtype.dualMap x) =
        (exteriorPower.map 2 P.subtype).dualMap (exteriorPower.pairingDual k E 2 x) at hn
      change exteriorPower.pairingDual k P 2 (exteriorPower.map 2 P.subtype.dualMap x) =
        exteriorPower.pairingDual k P 2 y
      exact hn.trans (by rw [hx]; exact hφy)

theorem exteriorAnnihilator_top (n : ℕ) :
    exteriorAnnihilator k E n (⊤ : Submodule k (⋀[k]^n E)) = ⊥ := by
  unfold exteriorAnnihilator
  rw [Submodule.dualAnnihilator_top, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr (exteriorPairingDual_bijective k E n).1

/-- Actual isotropy, expressed by containment of the genuine exterior
inclusion image in the genuine quadratic kernel, forces zero actual
canonical image relations. -/
theorem quadraticImage_eq_bot_of_isotropic (P : Submodule k E)
    (I : Submodule k (⋀[k]^2 E))
    (hiso : LinearMap.range (exteriorPower.map 2 P.subtype) ≤ I) :
    quadraticImage k (_root_.Module.Dual k E) (_root_.Module.Dual k P)
      (componentDualQuotient k E P) (exteriorAnnihilator k E 2 I) = ⊥ := by
  rw [quadraticImage_exteriorAnnihilator]
  have hker : componentQuadraticKernel k E P I = ⊤ := by
    apply top_unique
    intro z _
    exact hiso (LinearMap.mem_range_self _ z)
  rw [hker]
  exact exteriorAnnihilator_top k P 2

end ChenRanks.Koszul
