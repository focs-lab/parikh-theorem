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

/-! One-hole plugging: silent productions still add production nodes, and a
nested hole can have a different label from the outer context's root. -/

example : Complete unitGrammar
    ((ParseTree.node unitProduction [.hole 1]).plug (.node eraseProduction [])) ∧
    ((ParseTree.node unitProduction [.hole 1]).plug (.node eraseProduction [])).root =
      .nonterminal 0 ∧
    ((ParseTree.node unitProduction [.hole 1]).plug (.node eraseProduction [])).weight = 0 ∧
    ((ParseTree.node unitProduction [.hole 1]).plug (.node eraseProduction [])).productionSize = 2 := by
  have hE : OneHole unitGrammar (.node unitProduction [.hole 1]) 1 := by
    refine ⟨Valid.node (g := unitGrammar) _ _ (by simp [unitGrammar]) ?_ ?_, ?_⟩
    · intro c hc
      have h : c = .hole 1 := by simpa only [List.mem_singleton] using hc
      subst c
      exact Valid.hole (g := unitGrammar) (1 : ℕ)
    · simp [ParseTree.root, unitProduction]
    · simp [ParseTree.holes]
  have ht : Complete unitGrammar (.node eraseProduction []) := by
    refine ⟨Valid.node (g := unitGrammar) _ _ (by simp [unitGrammar]) (by simp) ?_, ?_⟩
    · simp [eraseProduction]
    · simp [ParseTree.holes]
  have h := plugging unitGrammar _ _ 1 hE ht rfl
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [h.2.2.1]
    funext a
    exact Fin.elim0 a
  · rw [h.2.2.2.1]
    simp [ParseTree.productionSize]

def outerPlugRule : ContextFreeRule Bool ℕ :=
  ⟨0, [.terminal false, .nonterminal 2, .terminal true]⟩
def middlePlugRule : ContextFreeRule Bool ℕ := ⟨2, [.nonterminal 1]⟩
def wordPlugRule : ContextFreeRule Bool ℕ := ⟨1, [.terminal true]⟩
abbrev plugGrammar : ContextFreeGrammar Bool :=
  ⟨ℕ, 0, {outerPlugRule, middlePlugRule, wordPlugRule}⟩
def nestedContext : ParseTree Bool ℕ :=
  .node outerPlugRule [.terminal false, .node middlePlugRule [.hole 1], .terminal true]
def insertedWordTree : ParseTree Bool ℕ := .node wordPlugRule [.terminal true]

example : Complete plugGrammar (nestedContext.plug insertedWordTree) ∧
    (nestedContext.plug insertedWordTree).root = .nonterminal 0 ∧
    (nestedContext.plug insertedWordTree).yield = [false, true, true] ∧
    (nestedContext.plug insertedWordTree).weight true = 2 ∧
    (nestedContext.plug insertedWordTree).productionSize = 3 ∧
    (nestedContext.plug insertedWordTree).support = {0, 1, 2} := by
  have hm : Valid plugGrammar (.node middlePlugRule [.hole 1]) := by
    refine Valid.node (g := plugGrammar) _ _ (by simp [plugGrammar]) ?_ ?_
    · intro c hc
      have h : c = .hole 1 := by simpa only [List.mem_singleton] using hc
      subst c
      exact Valid.hole (g := plugGrammar) (1 : ℕ)
    · simp [ParseTree.root, middlePlugRule]
  have hE : OneHole plugGrammar nestedContext 1 := by
    refine ⟨Valid.node (g := plugGrammar) _ _ (by simp [plugGrammar]) ?_ ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact .terminal false
      · exact hm
      · exact .terminal true
    · simp [ParseTree.root, outerPlugRule, middlePlugRule]
    · simp [nestedContext, ParseTree.holes]
  have ht : Complete plugGrammar insertedWordTree := by
    refine ⟨Valid.node (g := plugGrammar) _ _ (by simp [plugGrammar]) ?_ ?_, ?_⟩
    · intro c hc
      have h : c = .terminal true := by simpa only [List.mem_singleton] using hc
      subst c
      exact .terminal true
    · simp [ParseTree.root, wordPlugRule]
    · simp [insertedWordTree, ParseTree.holes]
  have h := plugging plugGrammar nestedContext insertedWordTree 1 hE ht rfl
  refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_⟩
  · simp [nestedContext, insertedWordTree, ParseTree.plug, ParseTree.yield]
  · rw [h.2.2.1]
    simp [nestedContext, insertedWordTree, ParseTree.weight, counts, ParseTree.yield]
  · rw [h.2.2.2.1]
    simp [nestedContext, insertedWordTree, ParseTree.productionSize]
  · rw [h.2.2.2.2]
    ext A
    simp [nestedContext, insertedWordTree, ParseTree.support, ParseTree.productionLabels,
      outerPlugRule, middlePlugRule, wordPlugRule]
    tauto

end SkeletonExamples
