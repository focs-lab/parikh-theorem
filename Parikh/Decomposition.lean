import Parikh.GrammarTrees
import Parikh.ParseTreePaths
import Parikh.TreePlugging
import Parikh.TreeReplacement
import Parikh.BoundedCutSupport

/-! A compact family of internal surgery/decomposition contracts.
Context identity, positions, roots and support survive until activation.
-/
namespace Parikh
variable {T : Type*}

/-- Insert around a selected occurrence, keeping the original subtree (`def:insertion`). -/
def Inserts (g : ContextFreeGrammar T) (t C t' : ParseTree T g.NT) : Prop :=
  Complete g t ∧ Complete g t' ∧ ∃ A, Cycle g C A ∧
    ∃ q u, t.subtree q = some u ∧ u.root = .nonterminal A ∧
      t.replaceAt q (C.plug u) = some t'

inductive InsertionSequence (g : ContextFreeGrammar T) :
    ParseTree T g.NT → List (ParseTree T g.NT) → ParseTree T g.NT → Prop where
  | nil (t) : InsertionSequence g t [] t
  | cons {t C next Cs final} (step : Inserts g t C next)
      (rest : InsertionSequence g next Cs final) : InsertionSequence g t (C :: Cs) final

/-- Base trees are simple complete start trees; context height uses the active alphabet. -/
def IsBase (g : ContextFreeGrammar T) (B : ParseTree T g.NT) : Prop :=
  Complete g B ∧ B.root = .nonterminal g.initial ∧ B.Simple

def IsBoundedCycle (g : ContextFreeGrammar T) (C : ParseTree T g.NT) : Prop :=
  (∃ A, Cycle g C A) ∧ C.height ≤ (activeNonterminals g).card + 1

/-- Plugging preserves validity/root and adds weight/size/support (`lem:plug`). -/
theorem plugging [DecidableEq T] (g : ContextFreeGrammar T) (E t : ParseTree T g.NT)
    (A : g.NT) (hE : OneHole g E A) (ht : Complete g t)
    (hroot : t.root = .nonterminal A) :
    Complete g (E.plug t) ∧ (E.plug t).root = E.root ∧
      (E.plug t).weight = E.weight + t.weight ∧
      (E.plug t).productionSize = E.productionSize + t.productionSize ∧
      (E.plug t).support = E.support ∪ t.support := by
  obtain ⟨hvalid, hholes⟩ := hE
  have hsemantics := hvalid.plug_complete ht (by
    intro B hB
    have hBA : B = A := by simpa only [hholes, List.mem_singleton] using hB
    simpa only [hBA] using hroot)
  refine ⟨hsemantics.1, hsemantics.2, ?_, ?_, ?_⟩
  · funext a
    simpa only [ParseTree.weight, counts, Pi.add_apply, hholes,
      List.length_singleton, Nat.one_mul] using E.count_yield_plug t a
  · simpa only [hholes, List.length_singleton, Nat.one_mul]
      using E.productionSize_plug t
  · ext B
    simp [E.mem_support_plug t B, hholes]

/-- Support means an internal occurrence, including an empty-production node (`lem:enabled`). -/
theorem insertion_enabled (g : ContextFreeGrammar T) (t C : ParseTree T g.NT)
    (A : g.NT) (ht : Complete g t) (hC : Cycle g C A) :
    (∃ t', Inserts g t C t') ↔ A ∈ t.support := by
  classical
  constructor
  · rintro ⟨t', _, _, B, hCB, q, u, hpos, hu, _⟩
    have hBA : B = A := Symbol.nonterminal.inj (hCB.2.1.symm.trans hC.2.1)
    subst B
    exact (ht.mem_support_iff_subtree A).mpr ⟨q, u, hpos, hu⟩
  · intro hA
    obtain ⟨q, u, hpos, hu⟩ := (ht.mem_support_iff_subtree A).mp hA
    obtain ⟨huc, E, hE, _, _, hreplace⟩ := ht.subtree_context q u hpos A hu
    have hCu := plugging g C u A hC.1 huc hu
    have hCuRoot : (C.plug u).root = .nonterminal A := hCu.2.1.trans hC.2.1
    have hwhole := plugging g E (C.plug u) A hE hCu.1 hCuRoot
    exact ⟨E.plug (C.plug u), ht, hwhole.1, A, hC, q, u, hpos, hu,
      hreplace (C.plug u)⟩

/-- Exact accounting, including zero-weight cycles (`lem:insertion-laws`). -/
theorem insertion_accounting [DecidableEq T] (g : ContextFreeGrammar T)
    (t C t' : ParseTree T g.NT) (h : Inserts g t C t') :
    t'.root = t.root ∧ t'.weight = t.weight + C.weight ∧
      t'.productionSize = t.productionSize + C.productionSize ∧
      t'.support = t.support ∪ C.support := by
  obtain ⟨ht, _, A, hC, q, u, hpos, hu, hreplace⟩ := h
  obtain ⟨huc, E, hE, hroot, hplug, houter⟩ := ht.subtree_context q u hpos A hu
  have hCu := plugging g C u A hC.1 huc hu
  have hCuRoot : (C.plug u).root = .nonterminal A := hCu.2.1.trans hC.2.1
  have hbefore := plugging g E u A hE huc hu
  have hafter := plugging g E (C.plug u) A hE hCu.1 hCuRoot
  have hresult : E.plug (C.plug u) = t' :=
    Option.some.inj ((houter (C.plug u)).symm.trans hreplace)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hresult, hafter.2.1, hroot]
  · rw [← hresult, hafter.2.2.1, hCu.2.2.1, ← hplug, hbefore.2.2.1]
    ac_rfl
  · rw [← hresult, hafter.2.2.2.1, hCu.2.2.2.1, ← hplug, hbefore.2.2.2.1]
    omega
  · rw [← hresult, hafter.2.2.2.2, hCu.2.2.2.2, ← hplug, hbefore.2.2.2.2]
    ext B
    simp only [Set.mem_union]
    tauto

/-- Simple complete trees have bounded production height (`lem:simple-height`). -/
theorem simple_height (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) (hs : t.Simple) :
    t.height ≤ (activeNonterminals g).card := by
  classical
  obtain ⟨path, hp, hlen⟩ := t.exists_labelPath_height
  have hsubset : path.toFinset ⊆ activeNonterminals g := by
    intro A hA
    exact complete_support_active g t ht
      (t.labelPath_subset_support path hp A (List.mem_toFinset.mp hA))
  rw [← hlen, ← List.toFinset_card_of_nodup (hs path hp)]
  exact Finset.card_le_card hsubset

/-- A minimal non-simple subtree yields a bounded removable context (`lem:cut`). -/
theorem bounded_cut (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ smaller C, Complete g smaller ∧ smaller.root = t.root ∧
      IsBoundedCycle g C ∧ Inserts g smaller C t ∧
      smaller.productionSize < t.productionSize := by
  classical
  -- Descend to a non-simple occurrence whose side branches are all simple.
  obtain ⟨q, r, cs, hpos, hU, hsU, hsimple⟩ :=
    ht.exists_minimal_nonsimple_subtree hs
  let U : ParseTree T g.NT := .node r cs
  have hchildren : ∀ c ∈ cs, Complete g c := by
    obtain ⟨hv, hh⟩ := hU
    cases hv with
    | node _ _ hr hc roots =>
      have hholes : ∀ c ∈ cs, c.holes = [] := by
        simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
      exact fun c hc' => ⟨hc c hc', hholes c hc'⟩
  have hheight : U.height ≤ (activeNonterminals g).card + 1 := by
    have hchildheight : ∀ c ∈ cs, c.height ≤ (activeNonterminals g).card :=
      fun c hc => simple_height g c (hchildren c hc) (hsimple c hc)
    have hfold : (cs.map ParseTree.height).foldl max 0 ≤ (activeNonterminals g).card := by
      by_cases hcs : cs = []
      · simp [hcs]
      · have hne : cs.map ParseTree.height ≠ [] := fun h => hcs (List.map_eq_nil_iff.mp h)
        rw [List.foldl_max_eq_max hne, Nat.zero_max]
        apply (List.max_le_iff hne).mpr
        intro n hn
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact hchildheight c hc
    simpa only [U, ParseTree.height, Nat.add_comm] using Nat.add_le_add_left hfold 1
  -- The repeated root gives a proper descendant with the same root symbol.
  obtain ⟨c, hcmem, hrootmem⟩ :=
    ParseTree.exists_root_mem_child_support r cs hsU hsimple
  obtain ⟨p, v, hp, hvroot⟩ := ((hchildren c hcmem).mem_support_iff_subtree r.input).mp hrootmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcmem
  have hvpos : U.subtree (i :: p) = some v := by simp [U, ParseTree.subtree, hi, hp]
  obtain ⟨hv, C, hC, hCroot, hCplug, _⟩ := hU.subtree_context (i :: p) v hvpos r.input hvroot
  have hvsize : v.productionSize < U.productionSize :=
    (U.productionSize_subtree_bound (i :: p) v hvpos).2 (by simp)
  dsimp only [U] at hvsize
  have hCsize : 0 < C.productionSize := by
    have hsize := C.productionSize_plug v
    rw [hC.2, List.length_singleton, Nat.one_mul, hCplug] at hsize
    omega
  have hcycle : Cycle g C r.input := ⟨hC, hCroot, hCsize⟩
  have hCheight : C.height ≤ (activeNonterminals g).card + 1 := by
    have hle := C.height_le_height_plug v
    rw [hCplug] at hle
    exact hle.trans hheight
  -- Replace U by the descendant v; round-trip replacement certifies reconstruction.
  obtain ⟨_, E, hE, hEroot, hEplug, hreplace⟩ :=
    ht.subtree_context q U hpos r.input rfl
  have hsmall := hE.1.plug_complete hv (by
    intro A hA
    have heq : A = r.input := by simpa only [hE.2, List.mem_singleton] using hA
    simpa only [heq] using hvroot)
  obtain ⟨smaller, hreplace', hsub, hundo⟩ := t.subtree_replacement q U v hpos
  have heq : smaller = E.plug v := Option.some.inj (hreplace'.symm.trans (hreplace v))
  subst smaller
  refine ⟨E.plug v, C, hsmall.1, hsmall.2.trans hEroot, ⟨⟨r.input, hcycle⟩, hCheight⟩,
    ⟨hsmall.1, ht, r.input, hcycle, q, v, hsub, hvroot, ?_⟩, ?_⟩
  · rw [hCplug]
    exact hundo
  · have hbefore := E.productionSize_plug U
    have hafter := E.productionSize_plug v
    dsimp only [U] at hbefore
    simp only [hE.2, List.length_singleton, Nat.one_mul] at hbefore hafter
    rw [hEplug] at hbefore
    omega

/-- Exact reconstruction by strong induction on production count (`thm:decomposition`). -/
theorem decomposition (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) :
    ∃ B Cs, Complete g B ∧ B.root = t.root ∧ B.Simple ∧
      (∀ C ∈ Cs, IsBoundedCycle g C) ∧ InsertionSequence g B Cs t := by
  sorry

end Parikh
