import ChenRanks.ArrangementSingularCupSeparation
import ChenRanks.ActualArrangementRationalMaximalFamily
import ChenRanks.MaximalIsotropicKernelQuotientFamily

/-!
# The actual singular-cohomology maximal family of an arrangement

The equation-class equivalence transports the actual original logarithmic
subspaces to actual native first cohomology. Maximality is transported through
the genuine exterior-square map and the proved cup-kernel equality. No
component enumeration, first-cohomology basis, or separation premise is
supplied to the arrangement statements.
-/

noncomputable section

namespace ChenRanks.AffineArrangement

open Resonance

variable {d : ℕ} {ι : Type*} [Fintype ι] (A : AffineArrangement d ι)

abbrev SingularMaximalIsotropicFamily :=
  OriginalMaximalIsotropicFamily A.quadraticSingularCup

def rationalToSingularMaximalIsotropic
    (P : A.RationalMaximalIsotropicFamily) : A.SingularMaximalIsotropicFamily := by
  let e := A.equationWindingClassEquiv
  refine ⟨P.val.map e.toLinearMap, ?_, ?_⟩
  · apply (isMaximalIsotropic_map_equiv e A.quadraticSingularCup P.val).mpr
    change IsMaximalIsotropic (relationWedge A.equationQuadraticCup) P.val
    exact (A.equationQuadraticCup_maximal_iff_logarithmic P.val).mpr P.property.1
  · rw [finrank_submodule_map_equiv]
    exact P.property.2

def singularToRationalMaximalIsotropic
    (Q : A.SingularMaximalIsotropicFamily) : A.RationalMaximalIsotropicFamily := by
  let e := A.equationWindingClassEquiv
  let P := Q.val.comap e.toLinearMap
  have hm : P.map e.toLinearMap = Q.val :=
    Submodule.map_comap_eq_of_surjective e.surjective Q.val
  refine ⟨P, ?_, ?_⟩
  · apply (A.equationQuadraticCup_maximal_iff_logarithmic P).mp
    change IsMaximalIsotropic
      (relationWedge (A.quadraticSingularCup.comp (exteriorPower.map 2 e.toLinearMap))) P
    apply (isMaximalIsotropic_map_equiv e A.quadraticSingularCup P).mp
    rw [hm]
    exact Q.property.1
  · have hd := finrank_submodule_map_equiv e P
    rw [hm] at hd
    exact hd ▸ Q.property.2

/-- The actual original coefficient family and actual native H¹ family. -/
def rationalSingularMaximalIsotropicFamilyEquiv :
    A.RationalMaximalIsotropicFamily ≃ A.SingularMaximalIsotropicFamily where
  toFun := A.rationalToSingularMaximalIsotropic
  invFun := A.singularToRationalMaximalIsotropic
  left_inv P := by
    apply Subtype.ext
    change (P.val.map A.equationWindingClassEquiv.toLinearMap).comap
      A.equationWindingClassEquiv.toLinearMap = P.val
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp ha
      have he : b = a := A.equationWindingClassEquiv.injective hba
      simpa only [he] using hb
    · intro ha
      exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  right_inv Q := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_of_surjective A.equationWindingClassEquiv.surjective Q.val

theorem rationalSingularMaximalIsotropicFamilyEquiv_finrank
    (P : A.RationalMaximalIsotropicFamily) :
    Module.finrank ℂ (A.rationalSingularMaximalIsotropicFamilyEquiv P).val =
      Module.finrank ℂ P.val :=
  finrank_submodule_map_equiv A.equationWindingClassEquiv P.val

def rationalSingularMaximalDimensionFiberEquiv (m : ℕ) :
    {P : A.RationalMaximalIsotropicFamily // Module.finrank ℂ P.val = m} ≃
      {Q : A.SingularMaximalIsotropicFamily // Module.finrank ℂ Q.val = m} :=
  A.rationalSingularMaximalIsotropicFamilyEquiv.subtypeEquiv
    (fun P => by rw [A.rationalSingularMaximalIsotropicFamilyEquiv_finrank P])

def singularMaximalIsotropicDimensionCount (m : ℕ) : ℕ :=
  originalMaximalIsotropicDimensionCount A.quadraticSingularCup
    (fun Q hQ hdim => A.singularCupKernel_separated Q hQ hdim) m

theorem singularMaximalIsotropicDimensionCount_eq_rational (m : ℕ) :
    A.singularMaximalIsotropicDimensionCount m =
      A.rationalMaximalIsotropicDimensionCount m := by
  classical
  letI := A.rationalMaximalIsotropicFamilyFintype
  letI := originalMaximalIsotropicFamilyFintype A.quadraticSingularCup
    (fun Q hQ hdim => A.singularCupKernel_separated Q hQ hdim)
  unfold singularMaximalIsotropicDimensionCount rationalMaximalIsotropicDimensionCount
    originalMaximalIsotropicDimensionCount
  exact (Fintype.card_congr (A.rationalSingularMaximalDimensionFiberEquiv m)).symm

end ChenRanks.AffineArrangement
