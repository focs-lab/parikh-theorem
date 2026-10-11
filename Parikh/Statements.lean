import Parikh.Construction
import Parikh.RegularRealization

/-! Accepted public contracts, proved incrementally as recorded in the proof ledger.
A successful build alone does not establish that all theorem obligations are complete.
-/
namespace Parikh
variable {T : Type*}

/-- The exact tree/context union equals the Mathlib grammar image (`thm:main`). -/
theorem treeRepresentation_eq [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language := by
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

/-- Forward Parikh theorem for Mathlib grammars (`thm:parikh-statement`).
No finiteness or decidable-equality assumption is imposed on `g.NT`.
-/
theorem grammar_image [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    IsSemilinearSet (image g.language) := by
  sorry

/-- A finite indexed witness with exact denotation, not merely containment (`thm:main`). -/
theorem grammar_witness [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language := by
  sorry

/-- Language-level specialization using Mathlib's context-free predicate. -/
theorem contextFree_image [Finite T] [DecidableEq T] (L : Language T) (hL : L.IsContextFree) :
    IsSemilinearSet (image L) := by
  sorry

/-- Every CFL has a DFA-regular language with the same image (`thm:parikh-statement`). -/
theorem regular_realization [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ image R = image g.language := by
  sorry

end Parikh
