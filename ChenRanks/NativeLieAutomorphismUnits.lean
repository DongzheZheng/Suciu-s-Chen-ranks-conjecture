import ChenRanks.NativeLieAutomorphismGroup

/-! The genuine native Lie automorphism group has a genuine faithful
representation by units in its actual original endomorphism ring. These
are the original linear maps and their original inverse maps, with the
actual composition law; no representation or faithfulness is supplied.
-/
noncomputable section
namespace ChenRanks.LieComparison
variable (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L]

/-- A true native Lie automorphism is a true unit of its original endomorphism ring. -/
def nativeLieAutomorphismUnitsEnd : NativeLieAutomorphismGroup k L →* (Module.End k L)ˣ where
  toFun f :=
    { val := f.toLinearEquiv.toLinearMap
      inv := f.symm.toLinearEquiv.toLinearMap
      val_inv := by
        apply LinearMap.ext
        intro x
        exact f.apply_symm_apply x
      inv_val := by
        apply LinearMap.ext
        intro x
        exact f.symm_apply_apply x }
  map_one' := by
    apply Units.ext
    rfl
  map_mul' f g := by
    apply Units.ext
    rfl

@[simp] theorem nativeLieAutomorphismUnitsEnd_apply
    (f : NativeLieAutomorphismGroup k L) (x : L) :
    (nativeLieAutomorphismUnitsEnd k L f : Module.End k L) x = f x := rfl

/-- The actual unit representation retains every original automorphism value. -/
theorem nativeLieAutomorphismUnitsEnd_injective :
    Function.Injective (nativeLieAutomorphismUnitsEnd k L) := by
  intro f g h
  apply LieEquiv.ext
  intro x
  exact congrArg (fun u : (Module.End k L)ˣ => (u : Module.End k L) x) h

end ChenRanks.LieComparison
