import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Computability.Language
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs

/-! Concrete counting and finite witnesses; `sec:statement`, `eq:word-add`.
The witness records indexed periods, including duplicates and zero vectors.
-/
open scoped Pointwise

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
  funext a
  exact List.count_append

/-- Indexed period sums are exactly the additive closure of the period values.
This reuses Mathlib's finite-range closure theorem, including repeated and zero periods. -/
theorem Component.denotation_eq_vadd_closure {T : Type*} (c : Component T) :
    c.denotation = c.base +ᵥ
      (AddSubmonoid.closure (Set.range c.periods.get) : Set (Vector T)) := by
  ext x
  simp only [Component.denotation, Set.mem_ofPred_eq, Set.mem_vadd_set,
    SetLike.mem_coe, vadd_eq_add, AddSubmonoid.mem_closure_range_iff_of_fintype]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩

/-- Bridge indexed coefficient sums to Mathlib's finitely generated additive closure. -/
theorem component_isLinearSet {T : Type*} (c : Component T) :
    IsLinearSet c.denotation := by
  exact ⟨c.base, Set.range c.periods.get, Set.finite_range _,
    c.denotation_eq_vadd_closure⟩

/-- Every explicit witness denotes a Mathlib semilinear set (`sec:statement`). -/
theorem witness_isSemilinearSet {T : Type*} (W : Witness T) :
    IsSemilinearSet W.denotation := by
  classical
  have h : W.denotation = ⋃ c ∈ W.toFinset, c.denotation := by
    ext v
    simp [Witness.denotation]
  rw [h]
  exact IsSemilinearSet.biUnion_finset fun c _ =>
    (component_isLinearSet c).isSemilinearSet

/-- Mathlib's abstract semilinearity has an exact finite witness as well. -/
theorem exists_witness {T : Type*} (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ W : Witness T, W.denotation = X := by
  classical
  have linear_witness : ∀ X : Set (Vector T), IsLinearSet X →
      ∃ c : Component T, c.denotation = X := by
    rintro X ⟨b, periods, hperiods, rfl⟩
    refine ⟨⟨b, hperiods.toFinset.toList⟩, ?_⟩
    rw [Component.denotation_eq_vadd_closure]
    have hrange : Set.range hperiods.toFinset.toList.get = periods := by
      ext p
      simp only [Set.mem_range, ← List.mem_iff_get, Finset.mem_toList,
        Set.Finite.mem_toFinset]
    simp only [hrange]
  rcases hX with ⟨S, hS, hlinear, rfl⟩
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact ⟨[], by ext v; simp [Witness.denotation]⟩
  | @insert X S hnot hS ih =>
    obtain ⟨c, hc⟩ := linear_witness X (hlinear X (by simp))
    obtain ⟨W, hW⟩ := ih (fun Y hY => hlinear Y (by simp [hY]))
    refine ⟨c :: W, ?_⟩
    have hcons : Witness.denotation (c :: W) = c.denotation ∪ W.denotation := by
      ext v
      simp [Witness.denotation]
    rw [hcons, hc, hW, Set.sUnion_insert]

end Parikh
