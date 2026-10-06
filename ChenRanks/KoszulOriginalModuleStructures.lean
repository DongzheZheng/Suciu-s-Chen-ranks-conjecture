import ChenRanks.KoszulObjects

/-! Cached native structures of the genuine original Koszul quotient.
Each dictionary is synthesized once on generic original data. Its
specializations retain the actual quotient group and scalar action. -/

noncomputable section

namespace ChenRanks.Koszul

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [_root_.Module k V]
variable (K : Submodule k (⋀[k]^2 V))

@[implicit_reducible] def originalModuleAddCommGroup : AddCommGroup (Module k V K) := inferInstance

@[implicit_reducible] def originalModuleScalarModule : _root_.Module k (Module k V K) := inferInstance

end ChenRanks.Koszul
