import Parikh
import Lean

/-! Export kernel expressions rather than matching theorem lines. Types include
universes, every implicit argument and section variable. Every declaration is
exported for the proof-dependency audit. The compatibility checker separately
excludes internal proof helpers; definition bodies and instances remain recorded.
-/
open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let project := match env.getModuleIdxFor? name with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "Parikh"
      | none => false
    if !project then continue
    let isProof ← liftTermElabM <| Meta.isProp info.type
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let axioms ← collectAxioms name
    let direct := (info.value? (allowOpaque := true)).any fun value =>
      value.getUsedConstants.contains ``sorryAx
    let value := if isProof then Json.null else
      match info.value? (allowOpaque := true) with
      | some v => Json.str (reprStr v)
      | none => Json.null
    let contract := Json.mkObj [
      ("kind", toJson kind),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("type", toJson (reprStr info.type)),
      ("value", value),
      ("reducibility", toJson (match info.hints with
        | .opaque => "opaque"
        | .abbrev => "abbrev"
        | .regular height => s!"regular:{height}")),
      ("instance", toJson (Meta.isInstanceCore env name)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial)]
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("contract", contract),
      ("directSorry", toJson direct),
      ("dependencies", toJson ((info.getUsedConstantsAsSet.toArray).map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile ".lake/contract-audit.json" (Json.arr rows).pretty
