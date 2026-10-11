import Parikh.FiniteRepresentation

/-! Shared support for the forward theorem and its regular-language specialization.
The existing public declarations stay in `Statements`; this avoids an import cycle.
-/
namespace Parikh
variable {T : Type*}

/-- The exact tree formula and its semilinearity together give the grammar image
(`thm:main`, `thm:parikh-statement`). No finite nonterminal assumption is needed. -/
theorem treeRepresentation_correct [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language ∧ IsSemilinearSet (image g.language) := by
  have heq : treeRepresentation g = image g.language := by
    classical
    ext v
    constructor
    · rintro ⟨B, D, hB, _, hD, hv⟩
      rw [← one_linear g B D hB.1 hD] at hv
      obtain ⟨t, Cs, hseq, _, hweight⟩ := hv
      obtain ⟨ht, hroot, _, _, _⟩ := hseq.accounting hB.1
      refine ⟨t.yield, ?_, hweight⟩
      exact (g.mem_language_iff t.yield).mpr
        ((derives_iff_tree g g.initial t.yield).mpr
          ⟨t, ht, hroot.trans hB.2.1, rfl⟩)
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨t, ht, hroot, hyield⟩ :=
        (derives_iff_tree g g.initial w).mp ((g.mem_language_iff w).mp hw)
      obtain ⟨B, Cs, hB, hBroot, hsimple, hbounded, hseq⟩ := decomposition g t ht
      have hD := hseq.contextsActivatable hB
      refine ⟨B, Cs.toFinset, ⟨hB, hBroot.trans hroot, hsimple⟩,
        fun C hC => hbounded C (List.mem_toFinset.mp hC), hD, ?_⟩
      rw [← one_linear g B Cs.toFinset hB hD]
      exact ⟨t, Cs, hseq, fun C => List.mem_toFinset.symm,
        by simp only [ParseTree.weight, hyield]⟩
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact treeRepresentation_isSemilinearSet g

end Parikh
