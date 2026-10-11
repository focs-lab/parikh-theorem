import Mathlib.Computability.Language
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs

/-! Concrete counting and finite witnesses; `sec:statement`, `eq:word-add`.
The witness records indexed periods, including duplicates and zero vectors.
-/
namespace Parikh

abbrev Vector (T : Type*) := T → ℕ

/-- Count occurrences with Mathlib's `List.count`; no order on the alphabet is needed. -/
def counts {T : Type*} [DecidableEq T] (w : List T) : Vector T := fun a => w.count a

/-- The exact image of a Mathlib language under terminal counting. -/
def image {T : Type*} [DecidableEq T] (L : Language T) : Set (Vector T) := counts '' L

/-- One base and an indexed finite list of periods (`sec:statement`). -/
structure Component (T : Type*) where
  base : Vector T
  periods : List (Vector T)

/-- A finite representation, independent of grammars and trace theory. -/
abbrev Witness (T : Type*) := List (Component T)

/-- Natural coefficients vary independently at every period-list position. -/
def Component.denotation {T : Type*} (c : Component T) : Set (Vector T) :=
  {v | ∃ k : Fin c.periods.length → ℕ,
    v = c.base + ∑ i : Fin c.periods.length, k i • c.periods[i]}

/-- Empty list denotes the empty set; this is an exact union, not an approximation. -/
def Witness.denotation {T : Type*} (W : Witness T) : Set (Vector T) :=
  {v | ∃ c ∈ W, v ∈ c.denotation}

/-- Concatenation adds count vectors (`eq:word-add`). -/
theorem counts_append {T : Type*} [DecidableEq T] (u v : List T) :
    counts (u ++ v) = counts u + counts v := by
  sorry

/-- Bridge indexed coefficient sums to Mathlib's finitely generated additive closure. -/
theorem component_isLinearSet {T : Type*} (c : Component T) :
    IsLinearSet c.denotation := by
  sorry

/-- Every explicit witness denotes a Mathlib semilinear set (`sec:statement`). -/
theorem witness_isSemilinearSet {T : Type*} (W : Witness T) :
    IsSemilinearSet W.denotation := by
  sorry

/-- Mathlib's abstract semilinearity has an exact finite witness as well. -/
theorem exists_witness {T : Type*} (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ W : Witness T, W.denotation = X := by
  sorry

end Parikh
