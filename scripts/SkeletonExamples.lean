import Parikh

/-! Small semantic proofs and executable evaluations. General correctness is
proved in the library; the activation example must pay for C before E.
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

/-! Bounded finiteness: with infinitely many ambient nonterminals and no rules,
the active height-zero family has precisely two terminals and the start hole.
Dropping the active-hole restriction makes even the height-zero family infinite. -/

example : {t : ParseTree Bool ℕ | ActiveOpen noProductionsGrammar t ∧ t.height ≤ 0} =
    {ParseTree.terminal false, ParseTree.terminal true, ParseTree.hole 37} := by
  classical
  ext t
  change ParseTree Bool noProductionsGrammar.NT at t
  constructor
  · rintro ⟨⟨hv, ha⟩, hh⟩
    cases t with
    | terminal a => cases a <;> simp
    | hole A =>
      have hA := ha A (by simp [ParseTree.holes])
      have heq : A = 37 := by
        simpa [activeNonterminals, noProductionsGrammar] using hA
      subst A
      simp
    | node r cs =>
      cases hv with
      | node _ _ hr _ _ => simp [noProductionsGrammar] at hr
  · intro ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    all_goals
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · first | exact Valid.terminal _ | exact Valid.hole _
      · simp [ParseTree.holes, activeNonterminals, noProductionsGrammar]
      · simp [ParseTree.height]

example : {t : ParseTree Bool ℕ | Valid noProductionsGrammar t ∧ t.height ≤ 0}.Infinite := by
  have hinj : Function.Injective (ParseTree.hole (T := Bool) (N := ℕ)) := by
    intro A B h
    exact ParseTree.hole.inj h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro t ⟨A, rfl⟩
  exact ⟨Valid.hole (g := noProductionsGrammar) A, by simp [ParseTree.height]⟩

/-! Bounded cut: both side branches exceed the simple-tree bound, while the
removed context is bounded. All terminal counts are zero, so size—not yield—decreases. -/

def tallSilentChild : ParseTree Bool ℕ :=
  .node loopRule [.node loopRule [.node loopRule [emptyChild]]]

def tallSiblingTree : ParseTree Bool ℕ := .node forkRule [tallSilentChild, tallSilentChild]

example : (activeNonterminals insertionGrammar).card + 1 < tallSiblingTree.height ∧
    ∃ smaller C, Complete insertionGrammar smaller ∧
      smaller.root = tallSiblingTree.root ∧ IsBoundedCycle insertionGrammar C ∧
      Inserts insertionGrammar smaller C tallSiblingTree ∧
      smaller.productionSize < tallSiblingTree.productionSize ∧
      smaller.weight = 0 ∧ C.weight = 0 := by
  classical
  have he : Complete insertionGrammar emptyChild := by
    refine ⟨Valid.node (g := insertionGrammar) _ [] (by simp [insertionGrammar])
      (by simp) (by simp [emptyRule]), ?_⟩
    simp [emptyChild, ParseTree.holes]
  have wrap (c : ParseTree Bool insertionGrammar.NT) (hc : Complete insertionGrammar c)
      (hroot : c.root = .nonterminal 1) :
      Complete insertionGrammar (.node loopRule [c]) := by
    refine ⟨Valid.node (g := insertionGrammar) _ [c] (by simp [insertionGrammar]) ?_ ?_, ?_⟩
    · intro d hd
      have heq : d = c := by simpa using hd
      exact heq.symm ▸ hc.1
    · simp [loopRule, hroot]
    · simp [ParseTree.holes, hc.2]
  have hchild : Complete insertionGrammar tallSilentChild :=
    wrap _ (wrap _ (wrap _ he rfl) rfl) rfl
  have ht : Complete insertionGrammar tallSiblingTree := by
    refine ⟨Valid.node (g := insertionGrammar) _ _ (by simp [insertionGrammar]) ?_ ?_, ?_⟩
    · intro d hd
      have heq : d = tallSilentChild := by simpa using hd
      exact heq.symm ▸ hchild.1
    · simp [ParseTree.root, tallSilentChild, forkRule, loopRule]
    · simp [tallSiblingTree, ParseTree.holes, hchild.2]
  have hs : ¬ tallSiblingTree.Simple := by
    simp [tallSiblingTree, tallSilentChild, emptyChild, ParseTree.Simple,
      ParseTree.labelPaths, forkRule, loopRule, emptyRule]
  obtain ⟨smaller, C, hsmaller, hroot, hbounded, hinsert, hsize⟩ :=
    bounded_cut insertionGrammar tallSiblingTree ht hs
  have haccount := insertion_accounting _ _ _ _ hinsert
  have hz : tallSiblingTree.weight = 0 := by
    ext a
    simp [tallSiblingTree, tallSilentChild, emptyChild, ParseTree.weight, counts, ParseTree.yield]
  refine ⟨?_, smaller, C, hsmaller, hroot, hbounded, hinsert, hsize, ?_, ?_⟩
  · simp [activeNonterminals, insertionGrammar, forkRule, loopRule, emptyRule,
      tallSiblingTree, tallSilentChild, emptyChild, ParseTree.height]
  all_goals
    ext a
    have hzero : smaller.weight a + C.weight a = 0 :=
      (congrFun haccount.2.1 a).symm.trans (congrFun hz a)
    change _ = (0 : ℕ)
    omega

/-! Exact decomposition also applies to non-start roots over infinite
nonterminals. A silent unit chain needs contexts despite its empty yield. -/

example : ∃ B Cs, Complete insertionGrammar B ∧ B.root = .nonterminal 1 ∧
    B.Simple ∧ B.weight = 0 ∧ (∀ C ∈ Cs, IsBoundedCycle insertionGrammar C) ∧
    Cs ≠ [] ∧ InsertionSequence insertionGrammar B Cs tallSilentChild ∧
    tallSilentChild.productionSize = B.productionSize + (Cs.map ParseTree.productionSize).sum := by
  have he : Complete insertionGrammar emptyChild :=
    ⟨Valid.node (g := insertionGrammar) _ [] (by simp [insertionGrammar])
      (by simp) (by simp [emptyRule]), by simp [emptyChild, ParseTree.holes]⟩
  have h1 := plugging insertionGrammar silentCycle emptyChild 1 insertion_data.2.1 he rfl
  have h2 := plugging insertionGrammar silentCycle (silentCycle.plug emptyChild) 1
    insertion_data.2.1 h1.1 (h1.2.1.trans insertion_data.2.2.1)
  have h3 := plugging insertionGrammar silentCycle
    (silentCycle.plug (silentCycle.plug emptyChild)) 1 insertion_data.2.1 h2.1
    (h2.2.1.trans insertion_data.2.2.1)
  have ht : Complete insertionGrammar tallSilentChild := by
    simpa [tallSilentChild, silentCycle, ParseTree.plug] using h3.1
  have hs : ¬ tallSilentChild.Simple := by
    simp [tallSilentChild, emptyChild, ParseTree.Simple, ParseTree.labelPaths, loopRule, emptyRule]
  obtain ⟨B, Cs, hB, hr, hsimple, hbounded, hseq⟩ :=
    decomposition insertionGrammar tallSilentChild ht
  have hn : Cs ≠ [] := by
    intro hnil
    subst Cs
    cases hseq
    exact hs hsimple
  have ha := hseq.accounting hB
  have hz : tallSilentChild.weight = 0 := by
    ext a
    simp [tallSilentChild, emptyChild, ParseTree.weight, counts, ParseTree.yield]
  refine ⟨B, Cs, hB, hr, hsimple, ?_, hbounded, hn, hseq, ha.2.2.2.1⟩
  ext a
  have hzero : B.weight a + (Cs.map ParseTree.weight).sum a = 0 :=
    (congrFun ha.2.2.1 a).symm.trans (congrFun hz a)
  change _ = (0 : ℕ)
  omega

/-! Main equality distinguishes an empty language from one containing the
empty word, including an empty terminal alphabet and infinite nonterminals. -/

example : treeRepresentation noProductionsGrammar = ∅ := by
  rw [treeRepresentation_eq]
  have hl := ContextFreeGrammar.language_eq_zero_of_forall_input_ne_initial
    (g := noProductionsGrammar) (by simp [noProductionsGrammar])
  simp [image, hl, Language.zero_def]

example : treeRepresentation unitGrammar = {0} := by
  rw [treeRepresentation_eq]
  ext v
  constructor
  · intro _
    apply Set.mem_singleton_iff.mpr
    funext a
    exact Fin.elim0 a
  · intro hv
    have heq : v = 0 := Set.mem_singleton_iff.mp hv
    subst v
    refine ⟨[], ?_, ?_⟩
    · apply (unitGrammar.mem_language_iff []).mpr
      exact (ContextFreeGrammar.Produces.single (g := unitGrammar) ⟨unitProduction,
        by simp [unitGrammar], ContextFreeRule.Rewrites.input_output⟩).trans
        (ContextFreeGrammar.Produces.single (g := unitGrammar) ⟨eraseProduction,
          by simp [unitGrammar], ContextFreeRule.Rewrites.input_output⟩)
    · funext a
      exact Fin.elim0 a

/-! Forward Parikh and exact witnesses: distinguish an unproductive grammar
from a grammar deriving the empty word over an empty alphabet. -/

example : IsSemilinearSet (image noProductionsGrammar.language) ∧
    ∃ W : Witness Bool, W.denotation = ∅ := by
  refine ⟨contextFree_image noProductionsGrammar.language ⟨noProductionsGrammar, rfl⟩, ?_⟩
  obtain ⟨W, hW⟩ := grammar_witness noProductionsGrammar
  refine ⟨W, ?_⟩
  have hl := ContextFreeGrammar.language_eq_zero_of_forall_input_ne_initial
    (g := noProductionsGrammar) (by simp [noProductionsGrammar])
  simpa [image, hl, Language.zero_def] using hW

example : ∃ W : Witness (Fin 0), W.denotation = image unitGrammar.language ∧
    0 ∈ W.denotation := by
  obtain ⟨W, hW⟩ := grammar_witness unitGrammar
  refine ⟨W, hW, ?_⟩
  rw [hW]
  refine ⟨[], ?_, ?_⟩
  · apply (unitGrammar.mem_language_iff []).mpr
    exact (ContextFreeGrammar.Produces.single (g := unitGrammar) ⟨unitProduction,
      by simp [unitGrammar], ContextFreeRule.Rewrites.input_output⟩).trans
      (ContextFreeGrammar.Produces.single (g := unitGrammar) ⟨eraseProduction,
        by simp [unitGrammar], ContextFreeRule.Rewrites.input_output⟩)
  · funext a
    exact Fin.elim0 a

/-! Expression images: empty unions differ from epsilon over an empty alphabet;
zero and repeated periods retain their semantics. Counts do not fix letter order. -/

def boolAlphabet : AlphabetOrder Bool :=
  ⟨[false, true], by decide, by intro a; cases a <;> simp⟩

def emptyAlphabet : AlphabetOrder (Fin 0) :=
  ⟨[], by simp, fun a => Fin.elim0 a⟩

example : image (witnessExpression boolAlphabet []).matches' = ∅ := by
  rw [witnessExpression_image]
  ext v
  simp [Witness.denotation]

example : image (witnessExpression emptyAlphabet
    [⟨0, [0, 0]⟩]).matches' = {0} := by
  rw [witnessExpression_image]
  ext v
  have hv : v = 0 := by funext a; exact Fin.elim0 a
  subst v
  simp [Witness.denotation, Component.denotation]

-- No periods gives the singleton base word, rather than an empty language.
example : (componentExpression boolAlphabet ⟨fun _ => 1, []⟩).matches' =
    {[false, true]} := by
  change (wordExpression (representative boolAlphabet (fun _ => 1))).matches' * 1 = _
  rw [mul_one, wordExpression_matches]
  rfl

def pairedComponent : Component Bool := ⟨0, [0, fun _ => 1, fun _ => 1]⟩

-- Both nonzero indexed periods contribute; the zero period can be repeated
-- arbitrarily. The image includes these counts but the language orders blocks.
example : counts [true, true, false, false] ∈
    image (witnessExpression boolAlphabet [pairedComponent]).matches' ∧
    [true, true, false, false] ∉
      (witnessExpression boolAlphabet [pairedComponent]).matches' := by
  constructor
  · rw [witnessExpression_image]
    refine ⟨pairedComponent, by simp, fun i => if i.val = 0 then 37 else 1, ?_⟩
    funext a
    cases a <;> decide
  · decide

/-! DFA regularity preserves the actual word language, including epsilon and
empty unions; equal Parikh counts still do not admit every letter order. -/

example : (witnessExpression emptyAlphabet []).matches'.IsRegular ∧
    (witnessExpression emptyAlphabet [⟨0, [0, 0]⟩]).matches'.IsRegular ∧
    [] ∈ (witnessExpression emptyAlphabet [⟨0, [0, 0]⟩]).matches' ∧
    [] ∉ (witnessExpression emptyAlphabet []).matches' := by
  exact ⟨witnessExpression_regular _ _, witnessExpression_regular _ _,
    by decide, by decide⟩

example : ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA Bool σ,
    M.accepts = (witnessExpression boolAlphabet [pairedComponent]).matches' ∧
      [false, true, false, true] ∈ M.accepts ∧
      [true, true, false, false] ∉ M.accepts := by
  obtain ⟨σ, hσ, M, hM⟩ := (witnessExpression_correct boolAlphabet [pairedComponent]).2
  refine ⟨σ, hσ, M, hM, ?_, ?_⟩
  · rw [hM]
    decide
  · rw [hM]
    decide

-- Equal-image realization of an unproductive grammar is actually empty,
-- even with infinitely many ambient nonterminals.
example : ∃ R : Language Bool, R.IsRegular ∧ R = 0 := by
  obtain ⟨R, hR, himage⟩ := regular_realization noProductionsGrammar
  have hl := ContextFreeGrammar.language_eq_zero_of_forall_input_ne_initial
    (g := noProductionsGrammar) (by simp [noProductionsGrammar])
  refine ⟨R, hR, ?_⟩
  ext w
  constructor
  · intro hw
    have hcounts : counts w ∈ image R := ⟨w, hw, rfl⟩
    rw [himage, hl] at hcounts
    simp [image, Language.zero_def] at hcounts
  · intro hw
    exact (Language.notMem_zero _ hw).elim

/-! A concrete DFA for `(false true)*`: the grammar adapter preserves word
order, while the specialization proves semilinearity of its Parikh image. -/
def alternatingDFA : DFA Bool (Fin 3) where
  step q a := if q = 0 ∧ a = false then 1 else if q = 1 ∧ a = true then 0 else 2
  start := 0
  accept := {0}

example : [] ∈ (dfaGrammar alternatingDFA).language ∧
    [false, true, false, true] ∈ (dfaGrammar alternatingDFA).language ∧
    [true, true, false, false] ∉ (dfaGrammar alternatingDFA).language ∧
    IsSemilinearSet (image alternatingDFA.accepts) := by
  rw [dfaGrammar_language]
  exact ⟨by simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, alternatingDFA],
    by simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, alternatingDFA],
    by simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, alternatingDFA],
    regular_image _ ⟨Fin 3, inferInstance, alternatingDFA, rfl⟩⟩

-- Correctness is for every starting state, including a noninitial state.
example : (dfaGrammar alternatingDFA).Derives [.nonterminal (1 : Fin 3)] [.terminal true] := by
  exact (dfaGrammar_derives_iff alternatingDFA 1 [true]).mpr
    (by simp [DFA.evalFrom, alternatingDFA])

def emptyAlphabetDFA (acceptEmpty : Bool) : DFA (Fin 0) Unit where
  step _ a := Fin.elim0 a
  start := ()
  accept := {_q | acceptEmpty = true}

example : [] ∈ (dfaGrammar (emptyAlphabetDFA true)).language ∧
    [] ∉ (dfaGrammar (emptyAlphabetDFA false)).language ∧
    IsSemilinearSet (image (emptyAlphabetDFA true).accepts) ∧
    IsSemilinearSet (image (emptyAlphabetDFA false).accepts) := by
  rw [dfaGrammar_language, dfaGrammar_language]
  exact ⟨by simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, emptyAlphabetDFA],
    by simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, emptyAlphabetDFA],
    regular_image _ ⟨Unit, inferInstance, emptyAlphabetDFA true, rfl⟩,
    regular_image _ ⟨Unit, inferInstance, emptyAlphabetDFA false, rfl⟩⟩

/-! Executable activation (`lem:activation-test`): the earlier support example
now runs an algorithm whose `correct` field proves the result is exact. -/
def finiteAdded : Bool → Finset ℕ := fun operation => if operation then {1} else {0, 1}

-- C enables E; E cannot introduce its own prerequisite before it is enabled.
example : (activationTest ℕ Bool).run required finiteAdded {0} {false, true} = true ∧
    (activationTest ℕ Bool).run required finiteAdded {0} {true} = false := by decide

example : Activatable required (fun c => (finiteAdded c : Set ℕ)) {0} {false, true} := by
  simpa only [Finset.coe_singleton] using
    ((activationTest ℕ Bool).correct required finiteAdded {0} {false, true}).mp (by decide)

example : ¬ Activatable required (fun c => (finiteAdded c : Set ℕ)) {0} {true} := by
  intro h
  have h' : Activatable required (fun c => (finiteAdded c : Set ℕ))
      (({0} : Finset ℕ) : Set ℕ) {true} := by simpa only [Finset.coe_singleton] using h
  have hrun := ((activationTest ℕ Bool).correct required finiteAdded {0} {true}).mpr h'
  have hfalse : (activationTest ℕ Bool).run required finiteAdded {0} {true} = false := by decide
  rw [hfalse] at hrun
  contradiction

-- Empty work succeeds even without labels. A blocked cycle does not bootstrap;
-- giving it one initial label makes the same operations activatable.
def cycleRequired : Bool → ℕ := fun c => if c then 1 else 0
def cycleAdded : Bool → Finset ℕ := fun c => if c then {0} else {1}

example : (activationTest ℕ Bool).run cycleRequired cycleAdded ∅ ∅ = true ∧
    (activationTest ℕ Bool).run cycleRequired cycleAdded ∅ {false, true} = false ∧
    (activationTest ℕ Bool).run cycleRequired cycleAdded {0} {false, true} = true := by decide

-- No operation adds its own required label. The chain uses the entire round
-- budget and both ambient types are infinite; only the input sets are finite.
example : activationRounds (id : ℕ → ℕ) (fun c => {c + 1}) 3 {0} (Finset.range 4) = false ∧
    (activationTest ℕ ℕ).run id (fun c => {c + 1}) {0} (Finset.range 4) = true := by decide

-- A whole enabled batch may add overlapping or empty support sets. Selecting
-- no new labels is still progress because the selected operations are removed.
example : (activationTest ℕ ℕ).run (fun _ => 0) (fun _ => ∅) {0} {2, 5, 8} = true ∧
    (activationTest ℕ ℕ).run (fun c => if c = 2 then 1 else 0)
      (fun _ => {1}) {0} {0, 1, 2} = true := by decide

-- Compiled evaluation supplements the kernel-checked examples and general proof.
#eval [(activationTest ℕ Bool).run required finiteAdded {0} {false, true},
  (activationTest ℕ Bool).run required finiteAdded {0} {true},
  (activationTest ℕ ℕ).run id (fun c => {c + 1}) {0} (Finset.range 4)]

/-! Executable bounded enumeration: ordered siblings, an empty production, a
unit cycle, a duplicate rule and an unused declared nonterminal. -/
def enumerationStartRule : ContextFreeRule (Fin 1) (Fin 3) :=
  ⟨0, [.terminal 0, .nonterminal 1]⟩
def enumerationEmptyRule : ContextFreeRule (Fin 1) (Fin 3) := ⟨1, []⟩
def enumerationLoopRule : ContextFreeRule (Fin 1) (Fin 3) := ⟨1, [.nonterminal 1]⟩
abbrev enumerationGrammar : EncodedGrammar :=
  ⟨1, 2, 0, [enumerationStartRule, enumerationEmptyRule, enumerationLoopRule, enumerationEmptyRule]⟩

-- Height zero includes every declared leaf, even the unused nonterminal 2.
example : ((boundedEnumeration.enumerate enumerationGrammar 0).map ParseTree.root) =
    [.terminal 0, .nonterminal 0, .nonterminal 1, .nonterminal 2] := by decide

-- Empty and unit productions count as production nodes. Duplicate rules may
-- repeat trees, while decoding the grammar collapses duplicate productions.
example : (boundedEnumeration.enumerate enumerationGrammar 1).length = 8 ∧
    (boundedEnumeration.enumerate enumerationGrammar 2).length = 14 ∧
    enumerationGrammar.decode.rules.card = 3 := by decide

def enumeratedCompleteTree : ParseTree (Fin 1) (Fin 3) :=
  .node enumerationStartRule [.terminal 0, .node enumerationEmptyRule []]

-- Apply the exact correctness field in both directions at the height boundary.
example : enumeratedCompleteTree ∈ boundedEnumeration.enumerate enumerationGrammar 2 ∧
    enumeratedCompleteTree ∉ boundedEnumeration.enumerate enumerationGrammar 1 := by
  have hv : Valid enumerationGrammar.decode enumeratedCompleteTree := by
    apply (Valid.node_iff enumerationGrammar.decode _ _).mpr
    refine ⟨?_, ?_, rfl⟩
    · change enumerationStartRule ∈ enumerationGrammar.rules.toFinset
      simp [enumerationGrammar]
    · intro c hc
      change c ∈ [.terminal (0 : Fin 1), .node enumerationEmptyRule []] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Valid.terminal (g := enumerationGrammar.decode) 0
      · apply (Valid.node_iff enumerationGrammar.decode _ _).mpr
        refine ⟨?_, ?_, rfl⟩
        · change enumerationEmptyRule ∈ enumerationGrammar.rules.toFinset
          simp [enumerationGrammar]
        · exact fun _ hc => (List.not_mem_nil hc).elim
  have hh : enumeratedCompleteTree.height = 2 := by
    change (ParseTree.node enumerationStartRule
      [.terminal (0 : Fin 1), .node enumerationEmptyRule []]).height = 2
    rw [ParseTree.height_node_eq]
    simp [ParseTree.height]
  refine ⟨(boundedEnumeration.correct enumerationGrammar 2 _).mpr ⟨hv, ?_⟩, ?_⟩
  · change enumeratedCompleteTree.height ≤ 2
    omega
  · intro hmem
    have hheight := ((boundedEnumeration.correct enumerationGrammar 1 _).mp hmem).2
    change enumeratedCompleteTree.height ≤ 1 at hheight
    omega

-- Reversing the same children violates the production's ordered RHS.
example : ParseTree.node enumerationStartRule [.hole 1, .terminal 0] ∉
    boundedEnumeration.enumerate enumerationGrammar 2 := by
  intro hmem
  have hv := ((boundedEnumeration.correct enumerationGrammar 2 _).mp hmem).1
  have hroots := ((Valid.node_iff enumerationGrammar.decode _ _).mp hv).2.2
  change [Symbol.nonterminal (1 : Fin 3), Symbol.terminal (0 : Fin 1)] =
    [.terminal 0, .nonterminal 1] at hroots
  cases hroots

-- With no terminals, epsilon is still a height-one production node, distinct
-- from the height-zero hole. With no productions, only declared leaves remain.
abbrev encodedEpsilonGrammar : EncodedGrammar := ⟨0, 0, 0, [⟨0, []⟩]⟩
abbrev encodedNoRulesGrammar : EncodedGrammar := ⟨0, 0, 0, []⟩

example : (boundedEnumeration.enumerate encodedEpsilonGrammar 0).length = 1 ∧
    (boundedEnumeration.enumerate encodedEpsilonGrammar 3).length = 2 ∧
    (boundedEnumeration.enumerate encodedNoRulesGrammar 3).length = 1 := by decide

#eval (List.range 3).map (fun H => (boundedEnumeration.enumerate enumerationGrammar H).length)
#eval (boundedEnumeration.enumerate encodedEpsilonGrammar 1).map
  (fun t => (t.height, t.holes.length))

/-! Quantitative bounds retain infinite ambient nonterminals and zero terminal
weights. Only the two active labels of `unitGrammar` enter the bound. -/
example : (grammarSize unitGrammar).positions = 4 ∧
    (grammarSize unitGrammar).trees = 625 := by
  classical
  simp [grammarSize, activeNonterminals, unitGrammar, unitProduction, eraseProduction,
    GrammarSize.positions, GrammarSize.trees, GrammarSize.records]

-- The certified families are exact, even with an empty alphabet and empty RHS.
example : ∃ bases cycles : Finset (ParseTree (Fin 0) ℕ),
    (∀ B, B ∈ bases ↔ IsBase unitGrammar B) ∧
    (∀ C, C ∈ cycles ↔ IsBoundedCycle unitGrammar C) ∧
    bases.card ≤ 625 ∧ cycles.card ≤ 625 := by
  obtain ⟨⟨bases, hb, hbc⟩, ⟨cycles, hc, hcc⟩, _⟩ := bounded_family_bounds unitGrammar
  have hK : (grammarSize unitGrammar).trees = 625 := by
    classical
    simp [grammarSize, activeNonterminals, unitGrammar, unitProduction, eraseProduction,
      GrammarSize.positions, GrammarSize.trees, GrammarSize.records]
  exact ⟨bases, cycles, hb, hc, by simpa [hK] using hbc, by simpa [hK] using hcc⟩

/-! Quantitative witness assembly: empty input families produce no components,
and distinct zero-weight contexts retain two independently indexed periods. -/
example : familyWitness noProductionsGrammar ∅ ∅ = [] := by
  classical
  simp [familyWitness]

example : ∃ D : Finset (ParseTree Bool ℕ), D.card = 2 ∧
    (contextComponent activationBase D).periods.length = 2 ∧
    norm (contextComponent activationBase D).base = 0 ∧
    ∀ p ∈ (contextComponent activationBase D).periods, norm p = 0 := by
  classical
  have hB : norm activationBase.weight ≤ 0 := by
    rw [ParseTree.norm_weight_eq_length]
    simp [activationBase, ParseTree.yield]
  have hD : ∀ C ∈ ({openingCycle, silentCycle} : Finset (ParseTree Bool ℕ)),
      norm C.weight ≤ 0 := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl <;> rw [ParseTree.norm_weight_eq_length]
    · simp [openingCycle, emptyChild, ParseTree.yield]
    · simp [silentCycle, ParseTree.yield]
  have hcard : ({openingCycle, silentCycle} : Finset (ParseTree Bool ℕ)).card = 2 := by
    simp [openingCycle, silentCycle, openingRule, loopRule]
  obtain ⟨hlen, hbase, hperiod⟩ := contextComponent_size_bounds activationBase _ 0 hB hD
  exact ⟨{openingCycle, silentCycle}, hcard, by simpa [hcard] using hlen, by simpa using hbase,
    fun p hp => Nat.eq_zero_of_le_zero (hperiod p hp)⟩

/-! Fixed-width encoding: a base at the top of the two-bit range and duplicate
periods retain separate entries. An empty alphabet contributes no entry bits. -/
abbrev bitBudget : GrammarSize := ⟨0, 1, 0, 0⟩
abbrev bitWitness : Witness Unit := [⟨fun _ => 3, [fun _ => 1, fun _ => 1]⟩]

example : bitBudget.coordinateBits = 2 ∧ entryBits bitBudget bitWitness = 6 ∧
    bitBudget.vectorBits = 48 := by decide

example : entryBits bitBudget bitWitness ≤ 48 ∧
    (∀ c ∈ bitWitness, ∀ a, c.base a < 4) ∧
    (∀ c ∈ bitWitness, ∀ p ∈ c.periods, ∀ a, p a < 4) := by
  apply witness_bit_bound bitBudget (by decide) bitWitness
  simp [WithinBounds, bitWitness, norm, GrammarSize.trees,
    GrammarSize.positions, GrammarSize.records, Finset.sum_range_succ]

example : ∃ W : Witness (Fin 0), W.length = 1 ∧
    entryBits ⟨0, 0, 0, 0⟩ W = 0 ∧ WithinBounds ⟨0, 0, 0, 0⟩ W := by
  let W : Witness (Fin 0) := [⟨fun _ => 0, [fun _ => 0]⟩]
  refine ⟨W, rfl, ?_, ?_⟩
  · decide
  · simp [W, WithinBounds, norm, GrammarSize.trees, GrammarSize.positions,
      GrammarSize.records]

/-! Certified compiler execution. The runtime retains context identity through
activation, removes duplicate syntax, and represents the empty word explicitly. -/
abbrev encodedSilentGrammar : EncodedGrammar :=
  ⟨0, 0, 0, [⟨0, []⟩, ⟨0, [.nonterminal 0]⟩]⟩
abbrev encodedRepeatedSilentGrammar : EncodedGrammar :=
  ⟨0, 0, 0, [⟨0, []⟩, ⟨0, [.nonterminal 0]⟩, ⟨0, [.nonterminal 0]⟩]⟩
abbrev encodedUnaryGrammar : EncodedGrammar :=
  ⟨1, 0, 0, [⟨0, []⟩, ⟨0, [.terminal 0, .nonterminal 0]⟩]⟩
abbrev encodedUnreachableGrammar : EncodedGrammar :=
  ⟨0, 1, 0, [⟨0, []⟩, ⟨1, [.nonterminal 1]⟩]⟩

-- Read the finite vector functions as coordinate lists for execution/display.
def numericalEntries {d : ℕ} (W : Witness (Fin d)) :
    List (List ℕ × List (List ℕ)) :=
  W.map fun c => (List.ofFn c.base, c.periods.map (fun p => List.ofFn p))

example : (compiler.compile encodedUnaryGrammar).denotation =
    image encodedUnaryGrammar.decode.language ∧
    WithinBounds encodedUnaryGrammar.size (compiler.compile encodedUnaryGrammar) :=
  ⟨compiler.correct encodedUnaryGrammar, compiler.bounded encodedUnaryGrammar⟩

-- Runtime assertions exercise the compiled tree-statistic functions. Their
-- semantic guarantees come from the kernel-checked compiler fields above.
#eval show IO Unit from do
  unless (compiler.compile encodedNoRulesGrammar).length == 0 do
    throw (IO.userError "empty grammar produced a component")
  unless numericalEntries (compiler.compile encodedEpsilonGrammar) == [([], [])] do
    throw (IO.userError "epsilon grammar lost the zero component")
  unless ((compiler.compile encodedSilentGrammar).map fun c => c.periods.length) == [0, 1, 1, 2] do
    throw (IO.userError "distinct silent contexts lost their period positions")
  unless numericalEntries (compiler.compile encodedSilentGrammar) ==
      numericalEntries (compiler.compile encodedRepeatedSilentGrammar) do
    throw (IO.userError "repeated productions changed the compiled example")
  unless numericalEntries (compiler.compile encodedUnreachableGrammar) == [([], [])] do
    throw (IO.userError "unreachable contexts passed activation")
  let unary := numericalEntries (compiler.compile encodedUnaryGrammar)
  unless unary == [([0], []), ([1], [[1]]), ([2], [[2]]), ([3], [[1], [2]])] do
    throw (IO.userError "unary grammar compilation produced unexpected entries")
  IO.println (repr unary)

end SkeletonExamples
