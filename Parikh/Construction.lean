import Parikh.Activation
import Mathlib.Data.Nat.Log

/-!
# What an effective construction must provide

Knowing that a finite witness exists does not yet give an algorithm for
computing it. This file specifies the finite input encoding, bounded tree
enumeration, compiler output, and quantitative guarantees such an algorithm
must satisfy.

`EncodedGrammar` supplies finite syntax. `BoundedEnumeration` and `Compiler`
package proposed algorithms with their required correctness proofs; implementing
values remain to be supplied. The size and bit bounds describe the intended
output budget. Consult `docs/PROOF_STATUS.md` for outstanding proofs.

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

/-- Bounded families and leaf norms have the paper's coarse syntax bounds (`lem:count-trees`). -/
theorem bounded_family_bounds {T : Type*} [Fintype T] [DecidableEq T]
    (g : ContextFreeGrammar T) :
    (∃ bases : Finset (ParseTree T g.NT),
      (∀ B, B ∈ bases ↔ IsBase g B) ∧ bases.card ≤ (grammarSize g).trees) ∧
    (∃ cycles : Finset (ParseTree T g.NT),
      (∀ C, C ∈ cycles ↔ IsBoundedCycle g C) ∧ cycles.card ≤ (grammarSize g).trees) ∧
    (∀ t, IsBase g t ∨ IsBoundedCycle g t → norm t.weight ≤ (grammarSize g).positions) := by
  sorry

/-- The guaranteed exact witness also satisfies all four bounds (`thm:size-bound`). -/
theorem bounded_witness {T : Type*} [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language ∧ WithinBounds (grammarSize g) W := by
  sorry

/-- Numerical entries fit the stated fixed-width bit budget (`eq:bit-bound`). -/
theorem witness_bit_bound {T : Type*} [Fintype T] (s : GrammarSize)
    (hd : s.terminals = Fintype.card T) (W : Witness T) (h : WithinBounds s W) :
    entryBits s W ≤ s.vectorBits ∧
      (∀ c ∈ W, ∀ a, c.base a < 2 ^ s.coordinateBits) ∧
      (∀ c ∈ W, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ s.coordinateBits) := by
  sorry

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
The future implementation must enumerate syntax, not use classical choice.
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
