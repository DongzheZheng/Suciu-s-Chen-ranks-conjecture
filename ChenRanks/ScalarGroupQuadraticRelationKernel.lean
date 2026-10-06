import ChenRanks.ScalarFirstLowerCentralCharacters
import ChenRanks.GroupCharacterSkewExteriorCocycle
import ChenRanks.ExteriorBidualDeterminantPairing

/-! The original group cup kernel and the actual lower-central bracket.
A functional of the true degree-two bracket gives a determinant exterior
form in the actual cup kernel. The bar primitive is proved in the native
original group complex, rather than supplied as a comparison hypothesis.
-/
noncomputable section
namespace ChenRanks
variable (k G : Type) [Field k] [CharZero k] [Group G]

/-- The actual first original bracket as an alternating map. -/
def scalarFirstBracketAlternating :
    scalarLowerCentralPiece k G 0 [⋀^Fin 2]→ₗ[k] scalarLowerCentralPiece k G 1 where
  toFun a := scalarLowerCentralPieceBracket k G 0 0 (a 0) (a 1)
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      change scalarLowerCentralPieceBracket k G 0 0 (a 0) (a 1) = 0
      rw [h]
      exact scalarLowerCentralFirstBracket_self k G (a 1)
    · change a 1 = a 0 at h
      change scalarLowerCentralPieceBracket k G 0 0 (a 0) (a 1) = 0
      rw [h]
      exact scalarLowerCentralFirstBracket_self k G (a 0)
    · exact (hij rfl).elim

def scalarFirstExteriorBracket :
    (⋀[k]^2 (scalarLowerCentralPiece k G 0)) →ₗ[k] scalarLowerCentralPiece k G 1 :=
  exteriorPower.alternatingMapLinearEquiv (scalarFirstBracketAlternating k G)

@[simp] theorem scalarFirstExteriorBracket_wedge
    (x y : scalarLowerCentralPiece k G 0) :
    scalarFirstExteriorBracket k G (exteriorWedge (k := k) x y) =
      scalarLowerCentralPieceBracket k G 0 0 x y := by
  simp [scalarFirstExteriorBracket, exteriorWedge, scalarFirstBracketAlternating]

/-- Genuine original group cup, transported only by its proved native
first-quotient/character equivalence. -/
def scalarFirstGroupQuadraticCup :
    (⋀[k]^2 (Module.Dual k (scalarLowerCentralPiece k G 0))) →ₗ[k]
      groupCohomology.H2 (groupTrivialCoefficients k G) :=
  (groupCharacterQuadraticCup k G).comp
    (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap)

def scalarFirstGroupCupKernel :
    Submodule k (⋀[k]^2 (Module.Dual k (scalarLowerCentralPiece k G 0))) :=
  (scalarFirstGroupQuadraticCup k G).ker

def nativeBarTwoEvaluation (g h : G) :
    groupCohomology.cocycles₂ (groupTrivialCoefficients k G) →ₗ[k] k where
  toFun c := c (g, h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Antisymmetric bar evaluation is the original determinant pairing. -/
theorem scalarDualExteriorSkewCocycle_evaluation
    (a : ⋀[k]^2 (Module.Dual k (scalarLowerCentralPiece k G 0))) (g h : G) :
    groupCharacterSkewExteriorCocycle k G
      (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap a)
        (g, h) =
      exteriorPower.pairingDual k (scalarLowerCentralPiece k G 0) 2 a
        (exteriorWedge (k := k) (GroupComparison.originalScalarFirstClass k G g)
          (GroupComparison.originalScalarFirstClass k G h)) := by
  have hm :
      (nativeBarTwoEvaluation k G g h).comp
        ((groupCharacterSkewExteriorCocycle k G).comp
          (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap)) =
      (exteriorPower.pairingDual k (scalarLowerCentralPiece k G 0) 2).flip
        (exteriorWedge (k := k) (GroupComparison.originalScalarFirstClass k G g)
          (GroupComparison.originalScalarFirstClass k G h)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    have hf : f = ![f 0, f 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hf]
    change groupCharacterSkewExteriorCocycle k G
      (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap
        (exteriorWedge (k := k) (f 0) (f 1))) (g, h) =
      exteriorPower.pairingDual k (scalarLowerCentralPiece k G 0) 2
        (exteriorWedge (k := k) (f 0) (f 1))
        (exteriorWedge (k := k) (GroupComparison.originalScalarFirstClass k G g)
          (GroupComparison.originalScalarFirstClass k G h))
    rw [exteriorPowerMap_exteriorWedge, groupCharacterSkewExteriorCocycle_wedge_apply]
    simp only [scalarFirstLowerCentralDualCharacters_groupClass, LinearEquiv.coe_coe,
      exteriorWedge, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact DFunLike.congr_fun hm a

variable [FiniteDimensional k (scalarLowerCentralPiece k G 0)]

/-- The exterior form canonically dual to a real second-degree functional. -/
def scalarBracketFunctionalExterior
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    ⋀[k]^2 (Module.Dual k (scalarLowerCentralPiece k G 0)) :=
  (Koszul.exteriorPairingDualEquiv k (scalarLowerCentralPiece k G 0) 2).symm
    (ell.comp (scalarFirstExteriorBracket k G))

@[simp] theorem scalarBracketFunctionalExterior_pairing
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    exteriorPower.pairingDual k (scalarLowerCentralPiece k G 0) 2
      (scalarBracketFunctionalExterior k G ell) =
      ell.comp (scalarFirstExteriorBracket k G) :=
  (Koszul.exteriorPairingDualEquiv k (scalarLowerCentralPiece k G 0) 2).apply_symm_apply _

/-- The actual cup-kernel membership is derived, not assumed. -/
theorem scalarBracketFunctionalExterior_mem_cupKernel
    (ell : Module.Dual k (scalarLowerCentralPiece k G 1)) :
    scalarBracketFunctionalExterior k G ell ∈ scalarFirstGroupCupKernel k G := by
  have hb :
      groupCharacterSkewExteriorCocycle k G
        (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap
          (scalarBracketFunctionalExterior k G ell)) =
        GroupComparison.scalarFirstBracketNativeCocycle k G ell := by
    apply Subtype.ext
    funext gh
    rcases gh with ⟨g, h⟩
    change groupCharacterSkewExteriorCocycle k G
      (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap
        (scalarBracketFunctionalExterior k G ell)) (g, h) =
      GroupComparison.scalarFirstBracketNativeCocycle k G ell (g, h)
    rw [scalarDualExteriorSkewCocycle_evaluation,
      scalarBracketFunctionalExterior_pairing, LinearMap.comp_apply,
      scalarFirstExteriorBracket_wedge,
      GroupComparison.scalarFirstBracketNativeCocycle_apply]
  have ht : (2 : k) • scalarFirstGroupQuadraticCup k G
      (scalarBracketFunctionalExterior k G ell) = 0 := by
    calc
      _ = groupCohomology.H2π (groupTrivialCoefficients k G)
          (groupCharacterSkewExteriorCocycle k G
            (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap
              (scalarBracketFunctionalExterior k G ell))) :=
        (DFunLike.congr_fun (groupCharacterSkewExteriorCocycle_native_class_map k G)
          (exteriorPower.map 2 (scalarFirstLowerCentralDualCharacters k G).toLinearMap
            (scalarBracketFunctionalExterior k G ell))).symm
      _ = 0 := by
        rw [hb]
        exact GroupComparison.scalarFirstBracketNativeCocycle_class_zero k G ell
  exact (smul_eq_zero.mp ht).resolve_left two_ne_zero

end ChenRanks
