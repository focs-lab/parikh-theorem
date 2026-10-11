import Parikh.Cli

private def usage : String :=
  "Usage: parikh [GRAMMAR.json|-]\n\nRead a finite grammar as JSON and print its semilinear witness as JSON.\nOmit the path, or use -, to read standard input.\nSee docs/CLI.md for the grammar and output formats."

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  if args == ["--help"] || args == ["-h"] then
    (← IO.getStdout).putStrLn usage
    return 0
  let source ← match args with
    | [] | ["-"] => pure (none : Option String)
    | [path] =>
      if path.startsWith "-" then
        stderr.putStrLn s!"parikh: unknown option '{path}'\n{usage}"
        return 2
      pure (some path)
    | _ =>
      stderr.putStrLn s!"parikh: expected at most one input path\n{usage}"
      return 2
  try
    let input ← match source with
      | none => (← IO.getStdin).readToEnd
      | some path => IO.FS.readFile path
    match Lean.Json.parse input with
    | .error e =>
      stderr.putStrLn s!"parikh: invalid JSON: {e}"
      return 2
    | .ok j =>
      match Parikh.Cli.runJson j with
      | .error e =>
        stderr.putStrLn s!"parikh: {e}"
        return 2
      | .ok output =>
        (← IO.getStdout).putStrLn output.pretty
        return 0
  catch e =>
    stderr.putStrLn s!"parikh: {e}"
    return 1
