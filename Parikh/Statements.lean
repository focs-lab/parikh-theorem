import Parikh.Construction
import Parikh.RegularRealization

/-! Proposed public contracts. Every proof is deliberately outstanding in this
first statement-skeleton milestone. A successful build does not prove Parikh's theorem.
-/
namespace Parikh
variable {T : Type*}

/-- The exact tree/context union equals the Mathlib grammar image (`thm:main`). -/
theorem treeRepresentation_eq [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language := by
  sorry

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
