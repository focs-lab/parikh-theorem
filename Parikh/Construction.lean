import Parikh.Activation
import Mathlib.Data.Nat.Log
import Parikh.BoundedFamilySupport
import Parikh.FiniteWitness

/-!
# What an effective construction must provide

Knowing that a finite witness exists does not yet give an algorithm for
computing it. This file specifies the finite input encoding, bounded tree
enumeration, compiler output, and quantitative guarantees such an algorithm
must satisfy.

`EncodedGrammar` supplies finite syntax. `BoundedEnumeration` and `Compiler`
package algorithms with their required correctness proofs. The former is
implemented by `boundedEnumeration` in `Parikh/BoundedEnumeration.lean`; a
compiler value remains to be supplied. The size and bit bounds describe the
intended output budget. Consult `docs/PROOF_STATUS.md` for outstanding proofs.

Source: `sec:effective`, `eq:bound-defs`, `thm:size-bound`, `eq:bit-bound`.
-/
namespace Parikh

/-- The paper's grammar parameters; `branching ≥ 1` is supplied by the size definitions. -/
structure GrammarSize where
  nonterminals : ℕ
  terminals : ℕ
  productions : ℕ
  branching : ℕ
  deriving Repr

/-- `M`, `q`, `K` in `eq:bound-defs`; production height at most `n+1`. -/
def GrammarSize.positions (s : GrammarSize) : ℕ :=
  ∑ i ∈ Finset.range (s.nonterminals + 2), s.branching ^ i

def GrammarSize.records (s : GrammarSize) : ℕ :=
  1 + s.terminals + s.nonterminals + s.productions

def GrammarSize.trees (s : GrammarSize) : ℕ := s.records ^ s.positions

noncomputable def grammarSize {T : Type*} [Fintype T] (g : ContextFreeGrammar T) : GrammarSize :=
  ⟨(activeNonterminals g).card, Fintype.card T, g.rules.card,
    max 1 (g.rules.sup fun r => r.output.length)⟩

def norm {T : Type*} [Fintype T] (v : Vector T) : ℕ := ∑ a, v a

/-- All four representation bounds, including duplicate/zero indexed periods (`thm:size-bound`). -/
def WithinBounds {T : Type*} [Fintype T] (s : GrammarSize) (W : Witness T) : Prop :=
  W.length ≤ s.trees * 2 ^ s.trees ∧
    ∀ c ∈ W, c.periods.length ≤ s.trees ∧
      norm c.base ≤ (s.trees + 1) * s.positions ∧
      ∀ p ∈ c.periods, norm p ≤ s.positions

/-- Fixed coordinate width and vector-entry budget, excluding length metadata (`eq:bit-bound`). -/
def GrammarSize.coordinateBits (s : GrammarSize) : ℕ :=
  max 1 (Nat.clog 2 ((s.trees + 1) * s.positions + 1))

def GrammarSize.vectorBits (s : GrammarSize) : ℕ :=
  s.trees * 2 ^ s.trees * (s.trees + 1) * s.terminals * s.coordinateBits

def entryBits {T : Type*} [Fintype T] (s : GrammarSize) (W : Witness T) : ℕ :=
  (W.map fun c => (c.periods.length + 1) * Fintype.card T * s.coordinateBits).sum

/-- Summing the terminal counts gives the length of a tree's terminal yield. -/
theorem ParseTree.norm_weight_eq_length {T N : Type*} [Fintype T] [DecidableEq T]
    (t : ParseTree T N) : norm t.weight = t.yield.length := by
  classical
  change (∑ a, t.yield.count a) = t.yield.length
  rw [← List.sum_toFinset_count_eq_length t.yield]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  exact List.count_eq_zero.mpr (fun h => ha (List.mem_toFinset.mpr h))

/-- Bounded families and leaf norms have the paper's coarse syntax bounds (`lem:count-trees`). -/
theorem bounded_family_bounds {T : Type*} [Fintype T] [DecidableEq T]
    (g : ContextFreeGrammar T) :
    (∃ bases : Finset (ParseTree T g.NT),
      (∀ B, B ∈ bases ↔ IsBase g B) ∧ bases.card ≤ (grammarSize g).trees) ∧
    (∃ cycles : Finset (ParseTree T g.NT),
      (∀ C, C ∈ cycles ↔ IsBoundedCycle g C) ∧ cycles.card ≤ (grammarSize g).trees) ∧
    (∀ t, IsBase g t ∨ IsBoundedCycle g t → norm t.weight ≤ (grammarSize g).positions) := by
  classical
  let s := grammarSize g
  have hb : ∀ r ∈ g.rules, r.output.length ≤ s.branching := by
    intro r hr
    exact (Finset.le_sup (f := fun r => r.output.length) hr).trans (Nat.le_max_right _ _)
  have hbounded : ∀ t, IsBase g t ∨ IsBoundedCycle g t →
      ActiveOpen g t ∧ t.height ≤ s.nonterminals + 1 := by
    intro t ht
    rcases ht with hbase | hcycle
    · refine ⟨⟨hbase.1.1, ?_⟩, ?_⟩
      · simp [hbase.1.2]
      · exact (simple_height g t hbase.1 hbase.2.2).trans (Nat.le_succ _)
    · obtain ⟨⟨A, hcycle⟩, hh⟩ := hcycle
      refine ⟨⟨hcycle.1.1, ?_⟩, hh⟩
      intro B hB
      have hBA : B = A := by simpa only [hcycle.1.2, List.mem_singleton] using hB
      subst B
      exact hcycle.1.1.support_active hcycle.root_mem_support
  let family := treeFamily g (s.nonterminals + 1)
  have hmem : ∀ t, IsBase g t ∨ IsBoundedCycle g t → t ∈ family := by
    intro t ht
    obtain ⟨ho, hh⟩ := hbounded t ht
    exact mem_treeFamily g _ t ho hh
  have hcard : family.card ≤ s.trees := by
    exact card_treeFamily_le g s.branching s.records (by rfl) hb _
  refine ⟨⟨family.filter (IsBase g), ?_, ?_⟩,
    ⟨family.filter (IsBoundedCycle g), ?_, ?_⟩, ?_⟩
  · intro B
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hmem B (Or.inl h), h⟩⟩
  · exact (Finset.card_filter_le _ _).trans hcard
  · intro C
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hmem C (Or.inr h), h⟩⟩
  · exact (Finset.card_filter_le _ _).trans hcard
  · intro t ht
    obtain ⟨ho, hh⟩ := hbounded t ht
    rw [ParseTree.norm_weight_eq_length]
    exact yield_length_le_heightPositions g s.branching hb _ t ho.1 hh

/-- A component has one period per context and pays all first copies in its base. -/
theorem contextComponent_size_bounds {T N : Type*} [Fintype T] [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) (M : ℕ)
    (hB : norm B.weight ≤ M) (hD : ∀ C ∈ D, norm C.weight ≤ M) :
    (contextComponent B D).periods.length = D.card ∧
      norm (contextComponent B D).base ≤ (D.card + 1) * M ∧
      ∀ p ∈ (contextComponent B D).periods, norm p ≤ M := by
  classical
  refine ⟨by simp [contextComponent], ?_, ?_⟩
  · have hsum : norm (contextComponent B D).base =
        norm B.weight + ∑ C ∈ D, norm C.weight := by
      change (∑ a, (B.weight + ∑ C ∈ D, C.weight) a) = _
      simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib, norm]
      rw [Finset.sum_comm]
    rw [hsum]
    calc
      norm B.weight + ∑ C ∈ D, norm C.weight ≤ M + D.card * M :=
        Nat.add_le_add hB (by simpa using Finset.sum_le_sum hD)
      _ = (D.card + 1) * M := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  · intro p hp
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hp
    exact hD C (Finset.mem_toList.mp hC)

/-- The guaranteed exact witness also satisfies all four bounds (`thm:size-bound`). -/
theorem bounded_witness {T : Type*} [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language ∧ WithinBounds (grammarSize g) W := by
  classical
  obtain ⟨⟨bases, hb, hbcard⟩, ⟨cycles, hc, hccard⟩, hnorm⟩ := bounded_family_bounds g
  refine ⟨familyWitness g bases cycles, familyWitness_denotation g bases cycles hb hc, ?_⟩
  refine ⟨(familyWitness_length_le g bases cycles).trans ?_, ?_⟩
  · exact Nat.mul_le_mul hbcard (Nat.pow_le_pow_right (by omega) hccard)
  · intro c hmem
    obtain ⟨B, hB, D, hD, _, rfl⟩ := (mem_familyWitness g bases cycles c).mp hmem
    have hDcard : D.card ≤ (grammarSize g).trees := (Finset.card_le_card hD).trans hccard
    obtain ⟨hlen, hbase, hperiod⟩ := contextComponent_size_bounds B D (grammarSize g).positions
      (hnorm B (Or.inl ((hb B).mp hB)))
      (fun C hC => hnorm C (Or.inr ((hc C).mp (hD hC))))
    exact ⟨hlen.le.trans hDcard,
      hbase.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hDcard 1)), hperiod⟩

/-- Numerical entries fit the stated fixed-width bit budget (`eq:bit-bound`). -/
theorem witness_bit_bound {T : Type*} [Fintype T] (s : GrammarSize)
    (hd : s.terminals = Fintype.card T) (W : Witness T) (h : WithinBounds s W) :
    entryBits s W ≤ s.vectorBits ∧
      (∀ c ∈ W, ∀ a, c.base a < 2 ^ s.coordinateBits) ∧
      (∀ c ∈ W, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ s.coordinateBits) := by
  classical
  have hwidth : (s.trees + 1) * s.positions < 2 ^ s.coordinateBits := by
    apply lt_of_lt_of_le (Nat.lt_succ_self _)
    exact (Nat.le_pow_clog (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  have hcoordinate (v : Vector T) (a : T) : v a ≤ norm v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hpositions : s.positions ≤ (s.trees + 1) * s.positions := by
    simpa using Nat.mul_le_mul_right s.positions (Nat.le_add_left 1 s.trees)
  refine ⟨?_, ?_, ?_⟩
  · have hentries : entryBits s W ≤
        W.length * ((s.trees + 1) * s.terminals * s.coordinateBits) := by
      unfold entryBits
      have hsum := List.sum_le_length_nsmul
        (W.map fun c => (c.periods.length + 1) * Fintype.card T * s.coordinateBits)
        ((s.trees + 1) * s.terminals * s.coordinateBits) (by
          intro n hn
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
          rw [← hd]
          exact Nat.mul_le_mul_right _
            (Nat.mul_le_mul_right _ (Nat.add_le_add_right (h.2 c hc).1 1)))
      simpa only [List.length_map, Nat.nsmul_eq_mul] using hsum
    exact hentries.trans (by
      simpa only [GrammarSize.vectorBits, Nat.mul_assoc] using
        Nat.mul_le_mul_right ((s.trees + 1) * s.terminals * s.coordinateBits) h.1)
  · intro c hc a
    exact lt_of_le_of_lt ((hcoordinate c.base a).trans (h.2 c hc).2.1) hwidth
  · intro c hc p hp a
    exact lt_of_le_of_lt
      ((hcoordinate p a).trans (((h.2 c hc).2.2 p hp).trans hpositions)) hwidth

/-- Finite numeric syntax for the future executable compiler; unused symbols are allowed. -/
structure EncodedGrammar where
  terminalCount : ℕ
  extraNonterminalCount : ℕ
  initial : Fin (extraNonterminalCount + 1)
  rules : List (ContextFreeRule (Fin terminalCount) (Fin (extraNonterminalCount + 1)))

def EncodedGrammar.decode (g : EncodedGrammar) : ContextFreeGrammar (Fin g.terminalCount) :=
  ⟨Fin (g.extraNonterminalCount + 1), g.initial, g.rules.toFinset⟩

/-- Numeric bounds count the declared finite alphabet; duplicate productions are collapsed. -/
def EncodedGrammar.size (g : EncodedGrammar) : GrammarSize :=
  ⟨g.extraNonterminalCount + 1, g.terminalCount, g.rules.toFinset.card,
    max 1 ((g.rules.map fun r => r.output.length).foldl max 0)⟩

/-- Complete enumeration contract for finite encoded grammars (`lem:finite`).
Implemented by `boundedEnumeration`, which enumerates syntax by height.
-/
structure BoundedEnumeration where
  enumerate : (g : EncodedGrammar) → ℕ →
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
  correct : ∀ g H t, t ∈ enumerate g H ↔ Valid g.decode t ∧ t.height ≤ H

/-- Algorithm output contract: exact image, explicit finite data, and the four bounds.
A future executable value must use bounded enumeration and the activation test;
this structure by itself does not certify effectivity.
-/
structure Compiler where
  compile : (g : EncodedGrammar) → Witness (Fin g.terminalCount)
  correct : ∀ g, (compile g).denotation = image g.decode.language
  bounded : ∀ g, WithinBounds g.size (compile g)

end Parikh
