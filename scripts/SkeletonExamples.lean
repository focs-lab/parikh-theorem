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

/-! Repeats must retain the earlier enabling operation. Keeping only the last
occurrence would move the dependent operation before its prerequisite. -/
example : ActivationOrder required added {0} [false, true, false] ∧
    ¬ ActivationOrder required added {0} [true, false] := by
  simp [ActivationOrder, required, added]

example : Activatable required added {0} {false, true} := by
  have h : ActivationOrder required added {0} [false, true, false] := by
    simp [ActivationOrder, required, added]
  have hset : [false, true, false].toFinset = ({false, true} : Finset Bool) := by decide
  simpa only [hset] using first_occurrences required added {0} [false, true, false] h

-- First-occurrence reduction needs no assumption that an operation adds its own root.
def nonselfAdded : Bool → Set ℕ := fun operation => if operation then ∅ else {1}
example : Activatable required nonselfAdded {0} {false, true} := by
  have h : ActivationOrder required nonselfAdded {0} [false, true, false] := by
    simp [ActivationOrder, required, nonselfAdded]
  have hset : [false, true, false].toFinset = ({false, true} : Finset Bool) := by decide
  simpa only [hset] using
    first_occurrences required nonselfAdded {0} [false, true, false] h

-- Both operations occur, with independently chosen positive multiplicities.
example : ∃ cs : List Bool, ActivationOrder required added {0} cs ∧
    cs.count false = 3 ∧ cs.count true = 2 := by
  have h : Activatable required added {0} {false, true} := by
    refine ⟨[false, true], by simp, by simp, ?_⟩
    simp [ActivationOrder, required, added]
  obtain ⟨cs, hcs, _, hcounts⟩ := positive_multiplicities required added {0} {false, true}
    (by intro c hc; cases c <;> simp [required, added]) h
    (fun c => if c then 2 else 3) (by intro c hc; cases c <;> simp)
  exact ⟨cs, hcs, hcounts false (by simp), hcounts true (by simp)⟩

-- Multiplicity one supplies the initial copy and requires no extra repetitions.
example : ∃ cs : List Bool, ActivationOrder required added {0} cs ∧
    cs.count false = 1 ∧ cs.count true = 1 := by
  have h : Activatable required added {0} {false, true} := by
    refine ⟨[false, true], by simp, by simp, ?_⟩
    simp [ActivationOrder, required, added]
  obtain ⟨cs, hcs, _, hcounts⟩ := positive_multiplicities required added {0} {false, true}
    (by intro c hc; cases c <;> simp [required, added]) h (fun _ => 1) (by simp)
  exact ⟨cs, hcs, hcounts false (by simp), hcounts true (by simp)⟩

-- For an empty operation set, positivity is vacuous even for zero requested counts.
example : ∃ cs : List Bool, ActivationOrder required added (∅ : Set ℕ) cs ∧ cs = [] := by
  have h : Activatable required added ∅ ∅ :=
    ⟨[], by simp, by simp, by simp [ActivationOrder]⟩
  obtain ⟨cs, hcs, hmem, _⟩ := positive_multiplicities required added ∅ ∅
    (by simp) h (fun _ => 0) (by simp)
  refine ⟨cs, hcs, List.eq_nil_iff_forall_not_mem.mpr ?_⟩
  intro c
  simpa using hmem c

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

/-! Occurrence-based insertion: two siblings have the same label, both are empty
productions, and a zero-weight unit cycle wraps only the second occurrence. -/

def forkRule : ContextFreeRule Bool ℕ := ⟨0, [.nonterminal 1, .nonterminal 1]⟩
def emptyRule : ContextFreeRule Bool ℕ := ⟨1, []⟩
def loopRule : ContextFreeRule Bool ℕ := ⟨1, [.nonterminal 1]⟩
abbrev insertionGrammar : ContextFreeGrammar Bool := ⟨ℕ, 0, {forkRule, emptyRule, loopRule}⟩
def emptyChild : ParseTree Bool ℕ := .node emptyRule []
def repeatedTree : ParseTree Bool ℕ := .node forkRule [emptyChild, emptyChild]
def silentCycle : ParseTree Bool ℕ := .node loopRule [.hole 1]
def wrappedTree : ParseTree Bool ℕ :=
  .node forkRule [emptyChild, silentCycle.plug emptyChild]

theorem insertion_data : Complete insertionGrammar repeatedTree ∧
    Cycle insertionGrammar silentCycle 1 := by
  have hc : Valid insertionGrammar emptyChild :=
    Valid.node (g := insertionGrammar) _ [] (by simp [insertionGrammar])
      (by simp) (by simp [emptyRule])
  constructor
  · refine ⟨Valid.node (g := insertionGrammar) _ _ (by simp [insertionGrammar]) ?_ ?_, ?_⟩
    · intro c h
      have heq : c = emptyChild := by simpa using h
      exact heq.symm ▸ hc
    · simp [ParseTree.root, emptyChild, forkRule, emptyRule]
    · simp [repeatedTree, emptyChild, ParseTree.holes]
  · refine ⟨⟨Valid.node (g := insertionGrammar) _ _ (by simp [insertionGrammar]) ?_ ?_, ?_⟩,
      rfl, ?_⟩
    · intro c h
      have heq : c = .hole 1 := by simpa using h
      subst c
      exact Valid.hole (g := insertionGrammar) (1 : ℕ)
    · simp [ParseTree.root, loopRule]
    · simp [silentCycle, ParseTree.holes]
    · simp [silentCycle, ParseTree.productionSize]

example : (∃ t', Inserts insertionGrammar repeatedTree silentCycle t') ∧
    2 ∉ repeatedTree.support := by
  constructor
  · apply (insertion_enabled insertionGrammar repeatedTree silentCycle 1
      insertion_data.1 insertion_data.2).mpr
    simp [repeatedTree, emptyChild, ParseTree.support, ParseTree.productionLabels,
      forkRule, emptyRule]
  · simp [repeatedTree, emptyChild, ParseTree.support, ParseTree.productionLabels,
      forkRule, emptyRule]

example : Inserts insertionGrammar repeatedTree silentCycle wrappedTree ∧
    wrappedTree.subtree [0] = some emptyChild ∧
    wrappedTree.subtree [1] = some (silentCycle.plug emptyChild) ∧
    repeatedTree.replaceAt [2] (silentCycle.plug emptyChild) = none ∧
    wrappedTree.root = repeatedTree.root ∧ wrappedTree.weight = repeatedTree.weight ∧
    wrappedTree.productionSize = 4 ∧ wrappedTree.support = repeatedTree.support := by
  have hpos : repeatedTree.subtree [1] = some emptyChild := by
    simp [repeatedTree, ParseTree.subtree]
  obtain ⟨hc, E, hE, _, _, hr⟩ :=
    insertion_data.1.subtree_context [1] emptyChild hpos 1 rfl
  have hCu := plugging insertionGrammar silentCycle emptyChild 1 insertion_data.2.1 hc rfl
  have hcomplete := plugging insertionGrammar E (silentCycle.plug emptyChild) 1 hE hCu.1
    (hCu.2.1.trans insertion_data.2.2.1)
  have hreplace : repeatedTree.replaceAt [1] (silentCycle.plug emptyChild) =
      some wrappedTree := by simp [repeatedTree, wrappedTree, ParseTree.replaceAt]
  have heq := Option.some.inj ((hr (silentCycle.plug emptyChild)).symm.trans hreplace)
  have hi : Inserts insertionGrammar repeatedTree silentCycle wrappedTree :=
    ⟨insertion_data.1, heq ▸ hcomplete.1, 1, insertion_data.2, [1], emptyChild,
      hpos, rfl, hreplace⟩
  have ha := insertion_accounting _ _ _ _ hi
  refine ⟨hi, ?_, ?_, ?_, ha.1, ?_, ?_, ?_⟩
  · simp [wrappedTree, ParseTree.subtree]
  · simp [wrappedTree, ParseTree.subtree]
  · simp [repeatedTree, ParseTree.replaceAt]
  · rw [ha.2.1]
    have hz : silentCycle.weight = 0 := by
      funext a
      simp [silentCycle, ParseTree.weight, counts, ParseTree.yield]
    rw [hz, add_zero]
  · rw [ha.2.2.1]
    simp [repeatedTree, emptyChild, silentCycle, ParseTree.productionSize]
  · rw [ha.2.2.2]
    ext A
    simp [repeatedTree, emptyChild, silentCycle, ParseTree.support,
      ParseTree.productionLabels, forkRule, emptyRule, loopRule]

end SkeletonExamples
