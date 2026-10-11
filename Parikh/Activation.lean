import Parikh.Decomposition

/-! Activation is independent of grammar syntax. The added sets and required
labels remain indexed by operations, even when their eventual weights coincide.
-/
namespace Parikh

/-- Enabled support transitions for an ordered list of operations (`eq:activation`). -/
def ActivationOrder {N C : Type*} (required : C → N) (added : C → Set N) :
    Set N → List C → Prop
  | _, [] => True
  | U, c :: cs => required c ∈ U ∧ ActivationOrder required added (U ∪ added c) cs

/-- Each member must be introduced exactly once before arbitrary repeats. -/
def Activatable {N C : Type*} (required : C → N) (added : C → Set N)
    (U : Set N) (D : Finset C) : Prop :=
  ∃ order : List C, order.Nodup ∧ (∀ c, c ∈ order ↔ c ∈ D) ∧
    ActivationOrder required added U order

/-- A valid sequence's distinct first occurrences activate the same set (`lem:first-occurrence`). -/
theorem first_occurrences {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (cs : List C)
    (h : ActivationOrder required added U cs) :
    Activatable required added U cs.toFinset := by
  sorry

/-- After activation, every positive multiplicity is possible (`lem:multiplicities`). -/
theorem positive_multiplicities {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (D : Finset C)
    (hself : ∀ c ∈ D, required c ∈ added c) (h : Activatable required added U D)
    (m : C → ℕ) (hm : ∀ c ∈ D, 0 < m c) :
    ∃ cs : List C, ActivationOrder required added U cs ∧
      (∀ c, c ∈ cs ↔ c ∈ D) ∧ (∀ c ∈ D, cs.count c = m c) := by
  sorry

/-- A decidable finite-search implementation is a future value of this interface.
`lem:activation-test`: no choice of an enabled operation can cause a false rejection.
-/
structure ActivationTest (N C : Type*) [DecidableEq N] [DecidableEq C] where
  run : (C → N) → (C → Finset N) → Finset N → Finset C → Bool
  correct : ∀ required added U D,
    run required added U D = true ↔
      Activatable required (fun c => (added c : Set N)) (U : Set N) D

/-- Concrete context subsets do not need a `DecidableEq g.NT` public hypothesis. -/
def ContextsActivatable {T : Type*} (g : ContextFreeGrammar T)
    (B : RawTree T g.NT) (D : Finset (RawTree T g.NT)) : Prop :=
  ∃ order : List (RawTree T g.NT), order.Nodup ∧
    (∀ C, C ∈ order ↔ C ∈ D) ∧
    ∃ roots : RawTree T g.NT → g.NT,
      (∀ C ∈ D, Cycle g C (roots C)) ∧
      ActivationOrder roots RawTree.support B.support order

/-- Every selected context is paid once in the base (`eq:component-base`). -/
noncomputable def contextComponent {T : Type*} [DecidableEq T]
    (B : RawTree T N) (D : Finset (RawTree T N)) : Component T := by
  classical
  exact ⟨B.weight + ∑ C ∈ D, C.weight, D.toList.map RawTree.weight⟩

/-- The explicit finite-union formula, retaining context identities (`eq:main`). -/
def treeRepresentation {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T) :
    Set (Vector T) :=
  {v | ∃ B D, IsBase g B ∧ (∀ C ∈ D, IsBoundedCycle g C) ∧
    ContextsActivatable g B D ∧ v ∈ (contextComponent B D).denotation}

/-- One activatable subset gives exactly one linear component (`prop:one-linear`). -/
theorem one_linear {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T)
    (B : RawTree T g.NT) (D : Finset (RawTree T g.NT))
    (hB : Complete g B) (hD : ContextsActivatable g B D) :
    {v | ∃ t Cs, InsertionSequence g B Cs t ∧
      (∀ C, C ∈ Cs ↔ C ∈ D) ∧ t.weight = v} =
      (contextComponent B D).denotation := by
  sorry

end Parikh
