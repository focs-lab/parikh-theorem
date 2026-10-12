import Parikh.ExecutableCompiler
import Lean.Data.Json

/-!
# JSON adapters for the certified compiler

Input validation constructs the existing finite grammar encoding without
clamping labels. Output coordinates follow terminal-index order and retain
all component/period positions. The coordinate round trip is kernel checked.
-/
namespace Parikh
namespace Cli
open Lean

/-- Plain coordinate arrays for one output component. -/
structure CoordinateComponent where
  base : List ℕ
  periods : List (List ℕ)

/-- Read a finite vector in terminal-index order. -/
def vectorCoordinates {d : ℕ} (v : Vector (Fin d)) : List ℕ := List.ofFn v

/-- Interpret coordinates by terminal index. Missing coordinates are zero;
compiler output always has exactly `d` coordinates. -/
def coordinatesVector {d : ℕ} (xs : List ℕ) : Vector (Fin d) :=
  fun a => xs[a.val]?.getD 0

theorem coordinatesVector_vectorCoordinates {d : ℕ} (v : Vector (Fin d)) :
    coordinatesVector (vectorCoordinates v) = v := by
  funext a
  simp [coordinatesVector, vectorCoordinates, a.isLt]

/-- Preserve each indexed period, including equal and zero vectors. -/
def componentCoordinates {d : ℕ} (c : Component (Fin d)) : CoordinateComponent :=
  ⟨vectorCoordinates c.base, c.periods.map vectorCoordinates⟩

def coordinatesComponent {d : ℕ} (c : CoordinateComponent) : Component (Fin d) :=
  ⟨coordinatesVector c.base, c.periods.map coordinatesVector⟩

theorem coordinatesComponent_componentCoordinates {d : ℕ} (c : Component (Fin d)) :
    coordinatesComponent (componentCoordinates c) = c := by
  cases c
  simp [coordinatesComponent, componentCoordinates, coordinatesVector_vectorCoordinates,
    List.map_map, Function.comp_def, List.map_id']

def witnessCoordinates {d : ℕ} (W : Witness (Fin d)) : List CoordinateComponent :=
  W.map componentCoordinates

def coordinatesWitness {d : ℕ} (W : List CoordinateComponent) : Witness (Fin d) :=
  W.map coordinatesComponent

/-- The numeric representation preserves the entire witness, not only denotation. -/
theorem coordinatesWitness_witnessCoordinates {d : ℕ} (W : Witness (Fin d)) :
    coordinatesWitness (witnessCoordinates W) = W := by
  simp [coordinatesWitness, witnessCoordinates, List.map_map, Function.comp_def,
    coordinatesComponent_componentCoordinates, List.map_id']

/-- Compute the numeric representation using the certified compiler. -/
def compileCoordinates (g : EncodedGrammar) : List CoordinateComponent :=
  witnessCoordinates (compiler.compile g)

/-- Interpreting emitted coordinate arrays gives exactly the grammar's Parikh image. -/
theorem compileCoordinates_correct (g : EncodedGrammar) :
    (coordinatesWitness (d := g.terminalCount) (compileCoordinates g)).denotation =
      image g.decode.language := by
  rw [compileCoordinates, coordinatesWitness_witnessCoordinates]
  exact compiler.correct g

/-- Numeric output inherits all four bounds of the certified witness. -/
theorem compileCoordinates_bounded (g : EncodedGrammar) :
    WithinBounds g.size (coordinatesWitness (d := g.terminalCount) (compileCoordinates g)) := by
  rw [compileCoordinates, coordinatesWitness_witnessCoordinates]
  exact compiler.bounded g

/-- Validate one numeric label without reducing it modulo the alphabet size. -/
def parseIndex (count : ℕ) (path : String) (value : ℕ) : Except String (Fin count) :=
  if h : value < count then .ok ⟨value, h⟩
  else .error s!"{path}: label {value} must be below {count}"

theorem parseIndex_value {count : ℕ} {path : String} {value : ℕ} {i : Fin count}
    (h : parseIndex count path value = .ok i) : i.val = value := by
  unfold parseIndex at h
  split at h
  · cases Except.ok.inj h
    rfl
  · cases h

/-- Require the documented object fields and reject misspellings or extra keys. -/
def checkFields (path : String) (j : Json) (keys : List String) : Except String Unit := do
  let obj ← j.getObj?.mapError (fun e => s!"{path}: {e}")
  for (key, _) in obj.toList do
    if !keys.contains key then throw s!"{path}: unknown field '{key}'"
  for key in keys do
    let _ ← j.getObjVal? key |>.mapError (fun e => s!"{path}: {e}")
  return ()

def natural (path : String) (j : Json) : Except String ℕ :=
  j.getNat?.mapError (fun _ => s!"{path}: expected a nonnegative integer")

def field (path : String) (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key |>.mapError (fun e => s!"{path}: {e}")

def finiteLabel (count : ℕ) (path : String) (j : Json) : Except String (Fin count) := do
  let value ← natural path j
  parseIndex count path value

/-- Symbols are single-key objects, tagged as terminal or nonterminal. -/
def parseSymbol (d n : ℕ) (path : String) (j : Json) :
    Except String (Symbol (Fin d) (Fin n)) := do
  let obj ← j.getObj?.mapError (fun e => s!"{path}: {e}")
  match obj.toList with
  | [("terminal", value)] => return .terminal (← finiteLabel d s!"{path}.terminal" value)
  | [("nonterminal", value)] => return .nonterminal (← finiteLabel n s!"{path}.nonterminal" value)
  | _ => throw s!"{path}: expected exactly one 'terminal' or 'nonterminal' field"

def parseRule (d n : ℕ) (path : String) (j : Json) :
    Except String (ContextFreeRule (Fin d) (Fin n)) := do
  checkFields path j ["input", "output"]
  let lhs ← finiteLabel n s!"{path}.input" (← field path j "input")
  let rhs ← (← field path j "output").getArr?.mapError (fun e => s!"{path}.output: {e}")
  let symbols ← rhs.toList.zipIdx.mapM fun (symbol, i) =>
    parseSymbol d n s!"{path}.output[{i}]" symbol
  return ⟨lhs, symbols⟩

/-- Validate finite grammar syntax. At least one declared nonterminal is needed;
empty terminal alphabets, empty productions and repeated rules are permitted. -/
def parseGrammar (j : Json) : Except String EncodedGrammar := do
  checkFields "grammar" j ["terminalCount", "nonterminalCount", "initial", "rules"]
  let d ← natural "terminalCount" (← field "grammar" j "terminalCount")
  let n ← natural "nonterminalCount" (← field "grammar" j "nonterminalCount")
  match n with
  | 0 => throw "nonterminalCount: must be at least 1"
  | k + 1 =>
    let initial ← finiteLabel (k + 1) "initial" (← field "grammar" j "initial")
    let rules ← (← field "grammar" j "rules").getArr?.mapError (fun e => s!"rules: {e}")
    let decoded ← rules.toList.zipIdx.mapM fun (rule, i) => parseRule d (k + 1) s!"rules[{i}]" rule
    return ⟨d, k, initial, decoded⟩

def componentJson (c : CoordinateComponent) : Json :=
  Json.mkObj [("base", toJson c.base), ("periods", toJson c.periods)]

/-- JSON output contains only the terminal count and the computed coordinate data. -/
def outputJson (g : EncodedGrammar) : Json :=
  Json.mkObj [("terminalCount", toJson g.terminalCount),
    ("components", Json.arr ((compileCoordinates g).map componentJson).toArray)]

/-- Pure JSON boundary used by the command-line entry point. -/
def runJson (j : Json) : Except String Json := do
  let g ← parseGrammar j
  return outputJson g

/-- Successful validation selects exactly the JSON encoding of that grammar's
certified output, rather than a second compilation path. -/
theorem runJson_of_parseGrammar {j : Json} {g : EncodedGrammar}
    (h : parseGrammar j = .ok g) : runJson j = .ok (outputJson g) := by
  simp [runJson, h]

end Cli
end Parikh
