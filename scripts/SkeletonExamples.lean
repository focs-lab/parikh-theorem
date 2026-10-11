import Parikh

/-! Small kernel-checked evaluations, not proofs of the outstanding contracts.
The activation example from `sec:example` must pay for operation C before E.
-/
open Parikh

namespace SkeletonExamples

def required : Bool → ℕ := fun operation => if operation then 1 else 0
def added : Bool → Set ℕ := fun operation => if operation then {1} else {0, 1}

example : ActivationOrder required added {0} [false, true] := by
  simp [ActivationOrder, required, added]

example : ¬ ActivationOrder required added {0} [true] := by
  simp [ActivationOrder, required]

def emptyProduction : ContextFreeRule (Fin 0) Unit := ⟨(), []⟩
def emptyTree : ParseTree (Fin 0) Unit := .node emptyProduction []

example : emptyTree.productionSize = 1 ∧ emptyTree.height = 1 ∧
    emptyTree.holes = [] ∧ emptyTree.yield = [] := by
  simp [emptyTree, ParseTree.productionSize, ParseTree.height, ParseTree.holes, ParseTree.yield]

example : (ParseTree.hole () : ParseTree (Fin 0) Unit).support = ∅ := by
  ext A
  simp [ParseTree.support, ParseTree.productionLabels]

example : Witness.denotation ([] : Witness (Fin 0)) = ∅ := by
  ext v
  simp [Witness.denotation]

example : (witnessExpression ⟨[], by simp, fun a => Fin.elim0 a⟩ ([] : Witness (Fin 0))).matches' = (0 : Language (Fin 0)) := rfl

end SkeletonExamples
