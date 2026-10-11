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

/-! Tree realization of activation: an opening cycle introduces label 1.
Both cycles have zero weight, but their different roots make order matter. -/

def activationBaseRule : ContextFreeRule Bool ℕ := ⟨0, []⟩
def openingRule : ContextFreeRule Bool ℕ := ⟨0, [.nonterminal 0, .nonterminal 1]⟩
abbrev activationGrammar : ContextFreeGrammar Bool :=
  ⟨ℕ, 0, {activationBaseRule, openingRule, emptyRule, loopRule}⟩
def activationBase : ParseTree Bool ℕ := .node activationBaseRule []
def openingCycle : ParseTree Bool ℕ := .node openingRule [.hole 0, emptyChild]
def activationRoots (C : ParseTree Bool ℕ) : ℕ :=
  match C.root with
  | .nonterminal A => A
  | .terminal _ => 0

theorem activation_tree_data : Complete activationGrammar activationBase ∧
    Cycle activationGrammar openingCycle 0 ∧ Cycle activationGrammar silentCycle 1 := by
  have he : Valid activationGrammar emptyChild :=
    Valid.node (g := activationGrammar) _ [] (by simp [activationGrammar])
      (by simp) (by simp [emptyRule])
  refine ⟨⟨Valid.node (g := activationGrammar) _ [] (by simp [activationGrammar])
    (by simp) (by simp [activationBaseRule]), by simp [activationBase, ParseTree.holes]⟩,
    ⟨⟨?_, ?_⟩, rfl, ?_⟩, ⟨⟨?_, ?_⟩, rfl, ?_⟩⟩
  · refine Valid.node (g := activationGrammar) _ _ (by simp [activationGrammar]) ?_ ?_
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Valid.hole (g := activationGrammar) (0 : ℕ)
      · exact he
    · simp [ParseTree.root, openingRule, emptyChild, emptyRule]
  · simp [openingCycle, emptyChild, ParseTree.holes]
  · simp [openingCycle, emptyChild, ParseTree.productionSize]
  · refine Valid.node (g := activationGrammar) _ _ (by simp [activationGrammar]) ?_ ?_
    · intro c hc
      have heq : c = .hole 1 := by simpa using hc
      subst c
      exact Valid.hole (g := activationGrammar) (1 : ℕ)
    · simp [ParseTree.root, loopRule]
  · simp [silentCycle, ParseTree.holes]
  · simp [silentCycle, ParseTree.productionSize]

theorem activation_tree_cycles (cs : List (ParseTree Bool ℕ))
    (hcs : ∀ C ∈ cs, C = openingCycle ∨ C = silentCycle) :
    ∀ C ∈ cs, Cycle activationGrammar C (activationRoots C) := by
  intro C hC
  rcases hcs C hC with rfl | rfl
  · simpa [activationRoots, openingCycle, ParseTree.root, openingRule]
      using activation_tree_data.2.1
  · simpa [activationRoots, silentCycle, ParseTree.root, loopRule]
      using activation_tree_data.2.2

example : ∃ t, InsertionSequence activationGrammar activationBase
    [openingCycle, silentCycle, silentCycle] t ∧ Complete activationGrammar t ∧
    t.root = .nonterminal 0 ∧ t.weight = 0 ∧ t.productionSize = 5 ∧ t.support = {0, 1} := by
  have hcycles := activation_tree_cycles [openingCycle, silentCycle, silentCycle] (by simp)
  have horder : ActivationOrder activationRoots ParseTree.support activationBase.support
      [openingCycle, silentCycle, silentCycle] := by
    simp [ActivationOrder, activationRoots, activationBase, openingCycle, silentCycle,
      emptyChild, ParseTree.root, ParseTree.support, ParseTree.productionLabels,
      activationBaseRule, openingRule, emptyRule, loopRule]
  obtain ⟨t, hseq⟩ := (activationOrder_iff_insertionSequence (g := activationGrammar)
    activationRoots activationBase
    _ activation_tree_data.1 hcycles).mp horder
  obtain ⟨ht, hr, hw, hn, hs⟩ := hseq.accounting activation_tree_data.1
  refine ⟨t, hseq, ht, hr, ?_, ?_, ?_⟩
  · rw [hw]
    funext a
    simp [activationBase, openingCycle, silentCycle, emptyChild, ParseTree.weight,
      counts, ParseTree.yield]
  · rw [hn]
    simp [activationBase, openingCycle, silentCycle, emptyChild, ParseTree.productionSize]
  · rw [hs]
    ext A
    simp [activationBase, openingCycle, silentCycle, emptyChild, ParseTree.support,
      ParseTree.productionLabels, activationBaseRule, openingRule, emptyRule, loopRule]

example : ¬ ∃ t, InsertionSequence activationGrammar activationBase
    [silentCycle, openingCycle] t := by
  have hcycles := activation_tree_cycles [silentCycle, openingCycle] (by simp [or_comm])
  rw [← activationOrder_iff_insertionSequence (g := activationGrammar) activationRoots activationBase _
    activation_tree_data.1 hcycles]
  simp [ActivationOrder, activationRoots, activationBase, silentCycle, ParseTree.root,
    ParseTree.support, ParseTree.productionLabels, activationBaseRule, loopRule]

example : ∃ t, Complete activationGrammar t ∧ t.support = {0, 1} ∧
    (∃ t', Inserts activationGrammar t openingCycle t') ∧
    (∃ t', Inserts activationGrammar t silentCycle t') := by
  classical
  have hD : ContextsActivatable activationGrammar activationBase {openingCycle, silentCycle} := by
    refine ⟨[openingCycle, silentCycle], ?_, by simp, activationRoots, ?_, ?_⟩
    · simp [openingCycle, silentCycle, openingRule, loopRule]
    · intro C hC
      apply activation_tree_cycles [openingCycle, silentCycle] (by simp) C
      simpa using hC
    · simp [ActivationOrder, activationRoots, activationBase, openingCycle, silentCycle,
        emptyChild, ParseTree.root, ParseTree.support, ParseTree.productionLabels,
        activationBaseRule, openingRule, emptyRule, loopRule]
  obtain ⟨order, t, _, _, _, ht, _, _, hs, he⟩ := hD.realize activation_tree_data.1
  refine ⟨t, ht, ?_, he openingCycle (by simp), he silentCycle (by simp)⟩
  rw [hs]
  ext A
  simp [activationBase, openingCycle, silentCycle, emptyChild, ParseTree.support,
    ParseTree.productionLabels, activationBaseRule, openingRule, emptyRule, loopRule]

-- An empty context set also preserves a complete terminal-rooted base.
example : ∃ t : ParseTree Bool ℕ, Complete activationGrammar t ∧
    t.root = .terminal true ∧ t.weight = counts [true] ∧ t.support = ∅ := by
  classical
  have hB : Complete activationGrammar (.terminal true) :=
    ⟨.terminal true, by simp [ParseTree.holes]⟩
  have hD : ContextsActivatable activationGrammar (.terminal true) ∅ :=
    ⟨[], by simp, by simp, activationRoots, by simp, by simp [ActivationOrder]⟩
  obtain ⟨_, t, _, _, _, ht, hr, hw, hs, _⟩ := hD.realize hB
  refine ⟨t, ht, hr, ?_, ?_⟩
  · simpa [ParseTree.weight, ParseTree.yield] using hw
  · simpa [ParseTree.support, ParseTree.productionLabels] using hs

/-! One linear component: two distinct contexts have the same nonzero weight,
but one must open the other's root. Both must be paid for before repetitions. -/

def weightedOpeningRule : ContextFreeRule Bool ℕ :=
  ⟨0, [.nonterminal 0, .nonterminal 1, .terminal false]⟩
def weightedLoopRule : ContextFreeRule Bool ℕ :=
  ⟨1, [.nonterminal 1, .terminal false]⟩
abbrev weightedGrammar : ContextFreeGrammar Bool :=
  ⟨ℕ, 0, {activationBaseRule, emptyRule, weightedOpeningRule, weightedLoopRule}⟩
def weightedOpening : ParseTree Bool ℕ :=
  .node weightedOpeningRule [.hole 0, emptyChild, .terminal false]
def weightedLoop : ParseTree Bool ℕ :=
  .node weightedLoopRule [.hole 1, .terminal false]
noncomputable def weightedContexts : Finset (ParseTree Bool ℕ) := by
  classical
  exact {weightedOpening, weightedLoop}

theorem weighted_data : Complete weightedGrammar activationBase ∧
    ContextsActivatable weightedGrammar activationBase weightedContexts := by
  classical
  unfold weightedContexts
  have he : Valid weightedGrammar emptyChild :=
    Valid.node (g := weightedGrammar) _ [] (by simp [weightedGrammar])
      (by simp) (by simp [emptyRule])
  have ho : Cycle weightedGrammar weightedOpening 0 := by
    refine ⟨⟨Valid.node (g := weightedGrammar) _ _ (by simp [weightedGrammar]) ?_ ?_, ?_⟩,
      rfl, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Valid.hole (g := weightedGrammar) (0 : ℕ)
      · exact he
      · exact .terminal false
    · simp [ParseTree.root, weightedOpeningRule, emptyChild, emptyRule]
    · simp [weightedOpening, emptyChild, ParseTree.holes]
    · simp [weightedOpening, emptyChild, ParseTree.productionSize]
  have hl : Cycle weightedGrammar weightedLoop 1 := by
    refine ⟨⟨Valid.node (g := weightedGrammar) _ _ (by simp [weightedGrammar]) ?_ ?_, ?_⟩,
      rfl, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Valid.hole (g := weightedGrammar) (1 : ℕ)
      · exact .terminal false
    · simp [ParseTree.root, weightedLoopRule]
    · simp [weightedLoop, ParseTree.holes]
    · simp [weightedLoop, ParseTree.productionSize]
  refine ⟨⟨Valid.node (g := weightedGrammar) _ [] (by simp [weightedGrammar])
    (by simp) (by simp [activationBaseRule]), by simp [activationBase, ParseTree.holes]⟩,
    [weightedOpening, weightedLoop], ?_, by simp, activationRoots, ?_, ?_⟩
  · simp [weightedOpening, weightedLoop, weightedOpeningRule, weightedLoopRule]
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · simpa [activationRoots, weightedOpening, ParseTree.root, weightedOpeningRule] using ho
    · simpa [activationRoots, weightedLoop, ParseTree.root, weightedLoopRule] using hl
  · simp [ActivationOrder, activationRoots, activationBase, weightedOpening, weightedLoop,
      emptyChild, ParseTree.root, ParseTree.support, ParseTree.productionLabels,
      activationBaseRule, weightedOpeningRule, weightedLoopRule, emptyRule]

-- Exactly the words with at least two false terminals have the obtainable weights.
-- The minimum is two despite both contexts having the same period vector.
example (n : ℕ) : (∃ t Cs, InsertionSequence weightedGrammar activationBase Cs t ∧
    (∀ C, C ∈ Cs ↔ C ∈ weightedContexts) ∧
    t.weight = counts (List.replicate n false)) ↔ 2 ≤ n := by
  classical
  change counts (List.replicate n false) ∈ {v | ∃ t Cs,
    InsertionSequence weightedGrammar activationBase Cs t ∧
    (∀ C, C ∈ Cs ↔ C ∈ weightedContexts) ∧ t.weight = v} ↔ _
  rw [one_linear weightedGrammar activationBase _ weighted_data.1 weighted_data.2,
    contextComponent.mem_denotation_iff]
  have hne : weightedOpening ≠ weightedLoop := by
    simp [weightedOpening, weightedLoop, weightedOpeningRule, weightedLoopRule]
  have hb : activationBase.weight = 0 := by
    ext a
    simp [activationBase, ParseTree.weight, ParseTree.yield, counts]
  have ho : weightedOpening.weight = counts [false] := by
    ext a
    simp [weightedOpening, emptyChild, ParseTree.weight, ParseTree.yield, counts]
  have hl : weightedLoop.weight = counts [false] := by
    ext a
    simp [weightedLoop, ParseTree.weight, ParseTree.yield, counts]
  constructor
  · rintro ⟨k, hv⟩
    have hfalse := congrFun hv false
    simp [weightedContexts, hb, ho, hl, hne, counts] at hfalse
    omega
  · intro hn
    refine ⟨fun C => if C = weightedOpening then n - 2 else 0, ?_⟩
    ext a
    cases a <;> simp [weightedContexts, hb, ho, hl, hne, counts, List.count_replicate]
    omega

-- Zero-weight contexts remain required, while all obtainable weights are zero.
example : {v | ∃ t Cs, InsertionSequence insertionGrammar repeatedTree Cs t ∧
    (∀ C, C ∈ Cs ↔ C ∈ ({silentCycle} : Finset _)) ∧ t.weight = v} = {0} := by
  classical
  have hD : ContextsActivatable insertionGrammar repeatedTree {silentCycle} := by
    refine ⟨[silentCycle], by simp, by simp, activationRoots, ?_, ?_⟩
    · intro C hC
      have heq : C = silentCycle := by simpa using hC
      subst C
      simpa [activationRoots, silentCycle, ParseTree.root, loopRule] using insertion_data.2
    · simp [ActivationOrder, activationRoots, repeatedTree, silentCycle, emptyChild,
        ParseTree.root, ParseTree.support, ParseTree.productionLabels,
        forkRule, emptyRule, loopRule]
  rw [one_linear insertionGrammar repeatedTree _ insertion_data.1 hD]
  have hb : repeatedTree.weight = 0 := by
    ext a
    simp [repeatedTree, emptyChild, ParseTree.weight, ParseTree.yield, counts]
  have hc : silentCycle.weight = 0 := by
    ext a
    simp [silentCycle, ParseTree.weight, ParseTree.yield, counts]
  ext v
  simp [contextComponent.mem_denotation_iff, hb, hc]

-- Empty context sets preserve a terminal-rooted base with nonzero weight.
example : {v | ∃ t Cs, InsertionSequence activationGrammar (.terminal true) Cs t ∧
    (∀ C, C ∈ Cs ↔ C ∈ (∅ : Finset _)) ∧ t.weight = v} = {counts [true]} := by
  classical
  have hB : Complete activationGrammar (.terminal true) :=
    ⟨.terminal true, by simp [ParseTree.holes]⟩
  have hD : ContextsActivatable activationGrammar (.terminal true) ∅ :=
    ⟨[], by simp, by simp, activationRoots, by simp, by simp [ActivationOrder]⟩
  rw [one_linear activationGrammar (.terminal true) ∅ hB hD]
  ext v
  simp [contextComponent.mem_denotation_iff, ParseTree.weight, ParseTree.yield]

/-! Active support and simple-tree height: production nodes, rather than yield
length or the total number of label occurrences, determine the bound. -/

def unitChain : ParseTree (Fin 0) ℕ :=
  .node unitProduction [.node eraseProduction []]

-- Infinite nonterminals and an empty terminal alphabet: the height bound is tight.
example : Complete unitGrammar unitChain ∧ unitChain.Simple ∧ unitChain.yield = [] ∧
    unitChain.height = (activeNonterminals unitGrammar).card ∧ unitChain.height = 2 := by
  classical
  have he : Valid unitGrammar (.node eraseProduction []) :=
    Valid.node (g := unitGrammar) _ [] (by simp [unitGrammar])
      (by simp) (by simp [eraseProduction])
  have ht : Complete unitGrammar unitChain := by
    refine ⟨Valid.node (g := unitGrammar) _ _ (by simp [unitGrammar]) ?_ ?_, ?_⟩
    · intro c hc
      have heq : c = .node eraseProduction [] := by simpa using hc
      exact heq.symm ▸ he
    · simp [ParseTree.root, unitProduction, eraseProduction]
    · simp [unitChain, ParseTree.holes]
  have hs : unitChain.Simple := by
    simp [unitChain, ParseTree.Simple, ParseTree.labelPaths, unitProduction, eraseProduction]
  have hh := simple_height unitGrammar unitChain ht hs
  have hn : (activeNonterminals unitGrammar).card = 2 := by
    simp [activeNonterminals, unitGrammar, unitProduction, eraseProduction]
  have hlower : 2 ≤ unitChain.height := by simp [unitChain, ParseTree.height]
  refine ⟨ht, hs, by simp [unitChain, ParseTree.yield], ?_, ?_⟩ <;> omega

-- Repeated siblings are simple, although their total label list has a duplicate.
example : repeatedTree.Simple ∧ ¬ repeatedTree.productionLabels.Nodup ∧
    repeatedTree.height ≤ (activeNonterminals insertionGrammar).card ∧
    repeatedTree.productionSize > repeatedTree.height ∧
    repeatedTree.support ⊆ (activeNonterminals insertionGrammar : Set ℕ) := by
  have hs : repeatedTree.Simple := by
    simp [repeatedTree, emptyChild, ParseTree.Simple, ParseTree.labelPaths, forkRule, emptyRule]
  refine ⟨hs, ?_, simple_height insertionGrammar repeatedTree insertion_data.1 hs, ?_,
    complete_support_active insertionGrammar repeatedTree insertion_data.1⟩
  · simp [repeatedTree, emptyChild, ParseTree.productionLabels, forkRule, emptyRule]
  · simp [repeatedTree, emptyChild, ParseTree.productionSize, ParseTree.height]

-- Repeating the label along a branch violates simplicity, even at zero weight.
example : ¬ wrappedTree.Simple ∧
    (activeNonterminals insertionGrammar).card < wrappedTree.height := by
  classical
  constructor
  · simp [wrappedTree, silentCycle, emptyChild, ParseTree.plug, ParseTree.Simple,
      ParseTree.labelPaths, forkRule, loopRule, emptyRule]
  · simp [activeNonterminals, insertionGrammar, wrappedTree, silentCycle, emptyChild,
      ParseTree.plug, ParseTree.height, forkRule, loopRule, emptyRule]

abbrev noProductionsGrammar : ContextFreeGrammar Bool := ⟨ℕ, 37, ∅⟩

-- A terminal-only tree remains complete and simple even without productions.
example : Complete noProductionsGrammar (.terminal true) ∧
    (.terminal true : ParseTree Bool ℕ).Simple ∧
    (.terminal true : ParseTree Bool ℕ).height ≤
      (activeNonterminals noProductionsGrammar).card := by
  have ht : Complete noProductionsGrammar (.terminal true) :=
    ⟨.terminal true, by simp [ParseTree.holes]⟩
  have hs : (.terminal true : ParseTree Bool ℕ).Simple := by
    simp [ParseTree.Simple, ParseTree.labelPaths]
  exact ⟨ht, hs, simple_height noProductionsGrammar _ ht hs⟩

-- A valid hole outside the active alphabet has empty support, but is not ActiveOpen.
example : Valid noProductionsGrammar (.hole 99) ∧
    (.hole 99 : ParseTree Bool ℕ).support ⊆
      (activeNonterminals noProductionsGrammar : Set ℕ) ∧
    ¬ ActiveOpen noProductionsGrammar (.hole 99) := by
  have hv : Valid noProductionsGrammar (.hole 99) :=
    Valid.hole (g := noProductionsGrammar) (99 : ℕ)
  refine ⟨hv, hv.support_active, ?_⟩
  simp [ActiveOpen, ParseTree.holes, activeNonterminals, noProductionsGrammar]

end SkeletonExamples
