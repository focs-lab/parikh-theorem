import Parikh.Decomposition

/-! Exact accounting across a list of insertions (`cor:sequence`). The original
subtree is retained at each step, including in zero-weight cycles.
-/
namespace Parikh
variable {T : Type*}

/-- A nontrivial cycle has a production node at its root (`eq:cycle-root`). -/
theorem Cycle.root_mem_support {g : ContextFreeGrammar T} {C : ParseTree T g.NT}
    {A : g.NT} (hC : Cycle g C A) : A ∈ C.support := by
  have hsize := hC.2.2
  cases C with
  | terminal a => simp [ParseTree.productionSize] at hsize
  | hole B => simp [ParseTree.productionSize] at hsize
  | node r cs =>
    have hroot : r.input = A := by simpa only [ParseTree.root, Symbol.nonterminal.injEq] using hC.2.1
    simp [ParseTree.support, ParseTree.productionLabels, hroot]

/-- Every insertion sequence preserves completeness/root and exactly adds the
listed weights and production counts, while taking the union of supports. -/
theorem InsertionSequence.accounting [DecidableEq T] {g : ContextFreeGrammar T}
    {B t : ParseTree T g.NT} {Cs : List (ParseTree T g.NT)}
    (h : InsertionSequence g B Cs t) (hB : Complete g B) :
    Complete g t ∧ t.root = B.root ∧
      t.weight = B.weight + (Cs.map ParseTree.weight).sum ∧
      t.productionSize = B.productionSize + (Cs.map ParseTree.productionSize).sum ∧
      t.support = B.support ∪ ⋃ C ∈ Cs, C.support := by
  induction h with
  | nil B => exact ⟨hB, rfl, by simp, by simp, by simp⟩
  | @cons B C next Cs final step rest ih =>
    have hs := insertion_accounting g B C next step
    obtain ⟨hf, hr, hw, hn, hu⟩ := ih step.2.1
    refine ⟨hf, hr.trans hs.1, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      rw [hw, hs.2.1]
      ac_rfl
    · simp only [List.map_cons, List.sum_cons]
      rw [hn, hs.2.2.1]
      omega
    · rw [hu, hs.2.2.2]
      ext A
      simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons]
      aesop

end Parikh
