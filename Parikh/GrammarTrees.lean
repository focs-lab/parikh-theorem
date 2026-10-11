import Parikh.Counting
import Mathlib.Computability.ContextFreeGrammar

/-! Grammar-specific syntax missing from the pinned Mathlib. Production labels
and child order are retained; empty productions are nodes, not holes.
-/
namespace Parikh

/-- Concrete parse-tree syntax (`def:tree`), including open trees with holes.
Grammar validity and completeness are checked separately by `Valid` and `Complete`. -/
inductive ParseTree (T N : Type*) where
  | terminal (a : T)
  | hole (A : N)
  | node (rule : ContextFreeRule T N) (children : List (ParseTree T N))

namespace ParseTree
variable {T N : Type*}

def root : ParseTree T N → Symbol T N
  | .terminal a => .terminal a
  | .hole A => .nonterminal A
  | .node r _ => .nonterminal r.input

/-- Production labels are omitted from the frontier; holes appear as nonterminals. -/
def frontier : ParseTree T N → List (Symbol T N)
  | .terminal a => [.terminal a]
  | .hole A => [.nonterminal A]
  | .node _ children => (children.map frontier).flatten

/-- Terminal leaves in order; for a complete tree this is its yield. -/
def yield : ParseTree T N → List T
  | .terminal a => [a]
  | .hole _ => []
  | .node _ children => (children.map yield).flatten

def holes : ParseTree T N → List N
  | .terminal _ => []
  | .hole A => [A]
  | .node _ children => (children.map holes).flatten

/-- The termination measure counts productions, including silent/unit nodes. -/
def productionSize : ParseTree T N → ℕ
  | .terminal _ | .hole _ => 0
  | .node _ children => 1 + (children.map productionSize).sum

def height : ParseTree T N → ℕ
  | .terminal _ | .hole _ => 0
  | .node _ children => 1 + (children.map height).foldl max 0

def productionLabels : ParseTree T N → List N
  | .terminal _ | .hole _ => []
  | .node r children => r.input :: (children.map productionLabels).flatten

/-- Holes contribute no nonterminal to support (`def:statistics`). -/
def support (t : ParseTree T N) : Set N := {A | A ∈ t.productionLabels}

def weight [DecidableEq T] (t : ParseTree T N) : Vector T := counts t.yield

/-- All production-label paths, including prefixes; repeated siblings are allowed. -/
def labelPaths : ParseTree T N → List (List N)
  | .terminal _ | .hole _ => [[]]
  | .node r children => [r.input] ::
      ((children.map labelPaths).flatten.map (r.input :: ·))

def Simple (t : ParseTree T N) : Prop := ∀ path ∈ t.labelPaths, path.Nodup

/-- Plug all holes. The one-hole contract below makes this a single replacement. -/
def plug : ParseTree T N → ParseTree T N → ParseTree T N
  | .terminal a, _ => .terminal a
  | .hole _, t => t
  | .node r children, t => .node r (children.map (fun c => plug c t))

/-- Positions use zero-based child indices; invalid positions return `none`. -/
def subtree : ParseTree T N → List ℕ → Option (ParseTree T N)
  | t, [] => some t
  | .node _ children, i :: q => children[i]?.bind (fun t => subtree t q)
  | _, _ :: _ => none

def replaceAt : ParseTree T N → List ℕ → ParseTree T N → Option (ParseTree T N)
  | _, [], replacement => some replacement
  | .node r children, i :: q, replacement => do
      let child ← children[i]?
      let newChild ← replaceAt child q replacement
      return .node r (children.set i newChild)
  | _, _ :: _, _ => none

end ParseTree

variable {T : Type*}

/-- Use exactly Mathlib's production membership and right-hand-side symbols. -/
inductive Valid (g : ContextFreeGrammar T) : ParseTree T g.NT → Prop where
  | terminal (a) : Valid g (.terminal a)
  | hole (A) : Valid g (.hole A)
  | node (r children) (rule_mem : r ∈ g.rules)
      (children_valid : ∀ t ∈ children, Valid g t)
      (roots_match : children.map ParseTree.root = r.output) : Valid g (.node r children)

def Complete (g : ContextFreeGrammar T) (t : ParseTree T g.NT) : Prop :=
  Valid g t ∧ t.holes = []

def OneHole (g : ContextFreeGrammar T) (E : ParseTree T g.NT) (A : g.NT) : Prop :=
  Valid g E ∧ E.holes = [A]

def Cycle (g : ContextFreeGrammar T) (C : ParseTree T g.NT) (A : g.NT) : Prop :=
  OneHole g C A ∧ C.root = .nonterminal A ∧ 0 < C.productionSize

/-- The start and every nonterminal mentioned in a production: finite even if `g.NT` is infinite. -/
noncomputable def activeNonterminals (g : ContextFreeGrammar T) : Finset g.NT := by
  classical
  exact {g.initial} ∪ g.rules.biUnion (fun r =>
    {r.input} ∪ (r.output.filterMap fun s => match s with
      | .terminal _ => none
      | .nonterminal A => some A).toFinset)

/-- Arbitrary holes outside the active alphabet must be excluded from bounded enumeration. -/
def ActiveOpen (g : ContextFreeGrammar T) (t : ParseTree T g.NT) : Prop :=
  Valid g t ∧ ∀ A ∈ t.holes, A ∈ activeNonterminals g

/-- Concrete bridge to Mathlib's derivation relation, for every root (`prop:tree-word`, appendix A). -/
theorem derives_iff_tree (g : ContextFreeGrammar T) (A : g.NT) (w : List T) :
    g.Derives [.nonterminal A] (w.map Symbol.terminal) ↔
      ∃ t : ParseTree T g.NT,
        Complete g t ∧ t.root = .nonterminal A ∧ t.yield = w := by
  sorry

/-- Every production node in a complete tree belongs to the finite active alphabet. -/
theorem complete_support_active (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by
  sorry

/-- Finite terminals and finite productions suffice; no `Fintype g.NT` (`lem:finite`). -/
theorem bounded_open_finite [Finite T] (g : ContextFreeGrammar T) (H : ℕ) :
    {t : ParseTree T g.NT | ActiveOpen g t ∧ t.height ≤ H}.Finite := by
  sorry

end Parikh
