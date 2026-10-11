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

/-! Grammar/tree semantics checks: empty alphabets, empty productions, an infinite
nonterminal type with a unit rule, and ordered terminal/nonterminal siblings. -/

abbrev emptyGrammar : ContextFreeGrammar (Fin 0) :=
  ⟨Unit, (), {emptyProduction}⟩

example : emptyGrammar.Derives [.nonterminal ()] [] := by
  apply (derives_iff_tree emptyGrammar () []).mpr
  refine ⟨emptyTree, ⟨?_, ?_⟩, rfl, ?_⟩
  · exact Valid.node (g := emptyGrammar) emptyProduction [] (by simp [emptyGrammar])
      (by simp) (by simp [emptyProduction])
  · simp [emptyTree, ParseTree.holes]
  · simp [emptyTree, ParseTree.yield]

def unitProduction : ContextFreeRule (Fin 0) ℕ := ⟨0, [.nonterminal 1]⟩
def eraseProduction : ContextFreeRule (Fin 0) ℕ := ⟨1, []⟩
abbrev unitGrammar : ContextFreeGrammar (Fin 0) :=
  ⟨ℕ, 0, {unitProduction, eraseProduction}⟩

example : ∃ t : ParseTree (Fin 0) ℕ,
    Complete unitGrammar t ∧ t.root = .nonterminal 0 ∧ t.yield = [] := by
  apply (derives_iff_tree unitGrammar 0 []).mp
  exact (ContextFreeGrammar.Produces.single (g := unitGrammar) ⟨unitProduction,
    by simp [unitGrammar], ContextFreeRule.Rewrites.input_output⟩).trans
    (ContextFreeGrammar.Produces.single (g := unitGrammar) ⟨eraseProduction,
      by simp [unitGrammar], ContextFreeRule.Rewrites.input_output⟩)

def branchingProduction : ContextFreeRule Bool Unit :=
  ⟨(), [.terminal false, .nonterminal (), .terminal true, .nonterminal ()]⟩
def silentProduction : ContextFreeRule Bool Unit := ⟨(), []⟩
abbrev branchingGrammar : ContextFreeGrammar Bool :=
  ⟨Unit, (), {branchingProduction, silentProduction}⟩

example : ∃ t : ParseTree Bool Unit,
    Complete branchingGrammar t ∧ t.root = .nonterminal () ∧
      t.yield = [false, true] := by
  apply (derives_iff_tree branchingGrammar () [false, true]).mp
  have first : branchingGrammar.Produces branchingProduction.output
      [.terminal false, .terminal true, .nonterminal ()] := by
    refine ⟨silentProduction, by simp [branchingGrammar], ?_⟩
    simpa [branchingProduction, silentProduction] using
      (ContextFreeRule.Rewrites.input_output (r := silentProduction)).append_right
        [.terminal true, .nonterminal ()] |>.append_left [.terminal false]
  have last : branchingGrammar.Produces
      [.terminal false, .terminal true, .nonterminal ()]
      [.terminal false, .terminal true] := by
    refine ⟨silentProduction, by simp [branchingGrammar], ?_⟩
    simpa [silentProduction] using
      (ContextFreeRule.Rewrites.input_output (r := silentProduction)).append_left
        [.terminal false, .terminal true]
  exact (ContextFreeGrammar.Produces.single ⟨branchingProduction,
    by simp [branchingGrammar], ContextFreeRule.Rewrites.input_output⟩).trans
      (first.single.trans last.single)

end SkeletonExamples
