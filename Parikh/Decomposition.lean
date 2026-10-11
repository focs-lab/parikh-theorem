import Parikh.GrammarTrees

/-! A compact family of internal surgery/decomposition contracts.
Context identity, positions, roots and support survive until activation.
-/
namespace Parikh
variable {T : Type*}

/-- Insert around a selected occurrence, keeping the original subtree (`def:insertion`). -/
def Inserts (g : ContextFreeGrammar T) (t C t' : RawTree T g.NT) : Prop :=
  Complete g t ∧ Complete g t' ∧ ∃ A, Cycle g C A ∧
    ∃ q u, t.subtree q = some u ∧ u.root = .nonterminal A ∧
      t.replaceAt q (C.plug u) = some t'

inductive InsertionSequence (g : ContextFreeGrammar T) :
    RawTree T g.NT → List (RawTree T g.NT) → RawTree T g.NT → Prop where
  | nil (t) : InsertionSequence g t [] t
  | cons {t C next Cs final} (step : Inserts g t C next)
      (rest : InsertionSequence g next Cs final) : InsertionSequence g t (C :: Cs) final

/-- Base trees are simple complete start trees; context height uses the active alphabet. -/
def IsBase (g : ContextFreeGrammar T) (B : RawTree T g.NT) : Prop :=
  Complete g B ∧ B.root = .nonterminal g.initial ∧ B.Simple

def IsBoundedCycle (g : ContextFreeGrammar T) (C : RawTree T g.NT) : Prop :=
  (∃ A, Cycle g C A) ∧ C.height ≤ (activeNonterminals g).card + 1

/-- Plugging preserves validity/root and adds weight/size/support (`lem:plug`). -/
theorem plugging [DecidableEq T] (g : ContextFreeGrammar T) (E t : RawTree T g.NT)
    (A : g.NT) (hE : OneHole g E A) (ht : Complete g t)
    (hroot : t.root = .nonterminal A) :
    Complete g (E.plug t) ∧ (E.plug t).root = E.root ∧
      (E.plug t).weight = E.weight + t.weight ∧
      (E.plug t).productionSize = E.productionSize + t.productionSize ∧
      (E.plug t).support = E.support ∪ t.support := by
  sorry

/-- Support means an internal occurrence, including an empty-production node (`lem:enabled`). -/
theorem insertion_enabled (g : ContextFreeGrammar T) (t C : RawTree T g.NT)
    (A : g.NT) (ht : Complete g t) (hC : Cycle g C A) :
    (∃ t', Inserts g t C t') ↔ A ∈ t.support := by
  sorry

/-- Exact accounting, including zero-weight cycles (`lem:insertion-laws`). -/
theorem insertion_accounting [DecidableEq T] (g : ContextFreeGrammar T)
    (t C t' : RawTree T g.NT) (h : Inserts g t C t') :
    t'.root = t.root ∧ t'.weight = t.weight + C.weight ∧
      t'.productionSize = t.productionSize + C.productionSize ∧
      t'.support = t.support ∪ C.support := by
  sorry

/-- Simple complete trees have bounded production height (`lem:simple-height`). -/
theorem simple_height (g : ContextFreeGrammar T) (t : RawTree T g.NT)
    (ht : Complete g t) (hs : t.Simple) :
    t.height ≤ (activeNonterminals g).card := by
  sorry

/-- A minimal non-simple subtree yields a bounded removable context (`lem:cut`). -/
theorem bounded_cut (g : ContextFreeGrammar T) (t : RawTree T g.NT)
    (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ smaller C, Complete g smaller ∧ smaller.root = t.root ∧
      IsBoundedCycle g C ∧ Inserts g smaller C t ∧
      smaller.productionSize < t.productionSize := by
  sorry

/-- Exact reconstruction by strong induction on production count (`thm:decomposition`). -/
theorem decomposition (g : ContextFreeGrammar T) (t : RawTree T g.NT)
    (ht : Complete g t) :
    ∃ B Cs, Complete g B ∧ B.root = t.root ∧ B.Simple ∧
      (∀ C ∈ Cs, IsBoundedCycle g C) ∧ InsertionSequence g B Cs t := by
  sorry

end Parikh
