import ChenRanks.SingularCohomologyRepresentatives

/-!
# Original cochains underlying the native cocycle representatives

The native homology kernel uses the same original differential. These
maps prove that connection explicitly, including the actual boundaries
in positive degrees. No identification of cochain models is assumed.
-/

noncomputable section

open CategoryTheory

namespace ChenRanks.SingularCohomology

variable (k : Type) [Field k] (X : Type) [TopologicalSpace X]

/-- The actual native cocycle inclusion into the original cochains. -/
def cocycleCochain (n : ℕ) : cocycles k X n →ₗ[k] cochains k X n :=
  ((complex k X).sc n).moduleCatLeftHomologyData.i.hom

/-- The native singular short-complex kernel consists of original closed cochains. -/
theorem cocycleCochain_closed (n : ℕ) (a : cocycles k X n) :
    differential k X n (cocycleCochain k X n a) = 0 := by
  have ha := a.property
  change ((complex k X).d n ((ComplexShape.up ℕ).next n)).hom a.val = 0 at ha
  erw [CochainComplex.next] at ha
  dsimp only [complex] at ha
  erw [CochainComplex.of_d] at ha
  exact ha

/-- A genuinely closed original cochain is an actual native cocycle. -/
def toCocycle (n : ℕ) (a : cochains k X n) (ha : differential k X n a = 0) :
    cocycles k X n := by
  refine ⟨a, ?_⟩
  change ((complex k X).d n ((ComplexShape.up ℕ).next n)).hom a = 0
  erw [CochainComplex.next]
  dsimp only [complex]
  erw [CochainComplex.of_d]
  exact ha

/-- Passing to an actual native cocycle retains the exact original cochain. -/
theorem cocycleCochain_toCocycle (n : ℕ) (a : cochains k X n)
    (ha : differential k X n a = 0) :
    cocycleCochain k X n (toCocycle k X n a ha) = a := rfl

/-- Every original native cocycle is recovered from its actual cochain. -/
theorem toCocycle_cocycleCochain (n : ℕ) (a : cocycles k X n) :
    toCocycle k X n (cocycleCochain k X n a)
      (cocycleCochain_closed k X n a) = a := by
  apply Subtype.ext
  rfl

/-- The original degree-n coboundary, placed in the actual native
positive-degree cocycles using the native index isomorphism. -/
def boundaryCocycle (n : ℕ) : cochains k X n →ₗ[k] cocycles k X (n + 1) :=
  (((complex k X).sc (n + 1)).moduleCatToCycles).comp
    ((complex k X).xPrevIso (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)).inv.hom

/-- The actual boundary map in a positive degree has exactly the genuine differential. -/
theorem positive_boundary_cochain (n : ℕ) (a : cochains k X n) :
    cocycleCochain k X (n + 1) (boundaryCocycle k X n a) =
      differential k X n a := by
  have h := (complex k X).xPrevIso_comp_dTo
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
  have ha := congrArg (fun f => f.hom a) h
  change ((complex k X).d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom
    (((complex k X).xPrevIso
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)).inv.hom a) = _
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, complex,
    CochainComplex.of_d, ModuleCat.hom_ofHom] using ha

/-- Membership in actual positive-degree boundaries gives an original differential representative. -/
theorem mem_positive_boundaries_iff (n : ℕ) (a : cocycles k X (n + 1)) :
    a ∈ boundaries k X (n + 1) ↔
      ∃ b : cochains k X n, differential k X n b = cocycleCochain k X (n + 1) a := by
  constructor
  · rintro ⟨b, hb⟩
    let e := ((complex k X).xPrevIso
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)).toLinearEquiv
    refine ⟨e b, ?_⟩
    rw [← positive_boundary_cochain k X n (e b)]
    have hnative : boundaryCocycle k X n (e b) =
        ((complex k X).sc (n + 1)).moduleCatToCycles b := by
      change ((complex k X).sc (n + 1)).moduleCatToCycles (e.symm (e b)) = _
      rw [e.symm_apply_apply]
    rw [hnative]
    exact congrArg (cocycleCochain k X (n + 1)) hb
  · rintro ⟨b, hb⟩
    have hba : boundaryCocycle k X n b = a := by
      apply Subtype.ext
      change cocycleCochain k X (n + 1) (boundaryCocycle k X n b) =
        cocycleCochain k X (n + 1) a
      rw [positive_boundary_cochain]
      exact hb
    rw [← hba]
    exact ⟨_, rfl⟩

end ChenRanks.SingularCohomology
