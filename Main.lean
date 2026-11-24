import MAGLean.Kernel

open MAGLean.Kernel

def usage : String :=
  "MAGLean — Quality Control Auditor for Metagenome-Assembled Genomes\n\n" ++
  "Usage:\n" ++
  "  maglean [--json] <evidence.json> [evidence2.json ...]\n\n" ++
  "Options:\n" ++
  "  --json    Emit machine-readable JSON certificate(s) instead of text reports\n" ++
  "  --help    Show this usage message\n"

def processFile (jsonMode : Bool) (path : System.FilePath) : IO UInt32 := do
  let text ← try
    IO.FS.readFile path
  catch e =>
    IO.eprintln s!"Error reading '{path}': {e}"
    return 2
  match parseMAGEvidence text with
  | .error e =>
    IO.eprintln s!"Parse error in '{path}': {e}"
    return 2
  | .ok ev =>
    match auditMAG ev with
    | .error e =>
      IO.eprintln s!"Audit precondition error in '{path}': {e}"
      return 2
    | .ok cert =>
      if jsonMode then
        IO.println (renderJson cert).pretty
      else
        IO.println (renderReport cert)
      return 0

def main (args : List String) : IO UInt32 := do
  let rec parseArgs (jsonMode : Bool) (files : List String) : List String → IO (Option (Bool × List String))
    | [] => pure (some (jsonMode, files.reverse))
    | "--help" :: _ | "-h" :: _ => do
      IO.println usage
      pure none
    | "--json" :: rest => parseArgs true files rest
    | path :: rest => parseArgs jsonMode (path :: files) rest
  match ← parseArgs false [] args with
  | none => return 0
  | some (_, []) => do
    IO.eprintln usage
    return 1
  | some (jsonMode, files) => do
    let mut exitCode : UInt32 := 0
    for f in files do
      let rc ← processFile jsonMode f
      if rc != 0 then exitCode := rc
    return exitCode
