import Parikh.Construction
import Parikh.FiniteRepresentation
import Parikh.RegularRealization

/-!
# Using Parikh's theorem

Start with `contextFree_image` for a language known to be context-free, or
`grammar_image` for a concrete Mathlib grammar. Both conclude semilinearity.
`grammar_witness` supplies a finite list of linear components with exactly the
same image, and `regular_realization` supplies a DFA-regular language with it.

The proof assembles earlier modules through `treeRepresentation_eq`: the union
of activatable tree components is exactly the grammar image. One inclusion
reconstructs words from components; the other decomposes a derivation tree.
The public results do not require a finite ambient nonterminal type.

Witness and automaton existence are classical. Executable construction and the
remaining library obligations are described in `docs/PROOF_STATUS.md`.

Source: `thm:main`, `thm:parikh-statement`.
-/
namespace Parikh
variable {T : Type*}

/-- The exact tree/context union equals the Mathlib grammar image (`thm:main`). -/
theorem treeRepresentation_eq [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language := by
  classical
  ext v
  constructor
  · -- Realize a component vector by insertions, then read the resulting word.
    rintro ⟨B, D, hB, _, hD, hv⟩
    rw [← one_linear g B D hB.1 hD] at hv
    obtain ⟨t, Cs, hseq, _, hweight⟩ := hv
    obtain ⟨ht, hroot, _, _, _⟩ := hseq.accounting hB.1
    refine ⟨t.yield, ?_, hweight⟩
    exact (g.mem_language_iff t.yield).mpr
      ((derives_iff_tree g g.initial t.yield).mpr
        ⟨t, ht, hroot.trans hB.2.1, rfl⟩)
  · -- Decompose a word's derivation tree and collect the contexts it uses.
    rintro ⟨w, hw, rfl⟩
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
  rw [← treeRepresentation_eq g]
  exact treeRepresentation_isSemilinearSet g

/-- A finite indexed witness with exact denotation, not merely containment (`thm:main`). -/
theorem grammar_witness [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language := by
  exact exists_witness (image g.language) (grammar_image g)

/-- Language-level specialization using Mathlib's context-free predicate. -/
theorem contextFree_image [Finite T] [DecidableEq T] (L : Language T) (hL : L.IsContextFree) :
    IsSemilinearSet (image L) := by
  obtain ⟨g, rfl⟩ := hL
  exact grammar_image g

/-- Every CFL has a DFA-regular language with the same image (`thm:parikh-statement`). -/
theorem regular_realization [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ image R = image g.language := by
  exact converse (image g.language) (grammar_image g)

end Parikh
