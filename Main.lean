import Lean
import MAGLean.Kernel

open MAGLean.Kernel
open Lean Elab Term

/-- Bake the current git commit hash into the executable at compile time
(falling back to `"unknown"` if compiled outside a git working tree). -/
elab "gitCommitHash%" : term => do
  let hash ← try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short=12", "HEAD"] }
    if out.exitCode == 0 then pure out.stdout.trimAscii.toString else pure "unknown"
  catch _ =>
    pure "unknown"
  return mkStrLit hash

def buildGitCommit : String := gitCommitHash%

def usage : String :=
  "MAGLean — Quality Control Auditor for Metagenome-Assembled Genomes\n\n" ++
  "Usage:\n" ++
  "  maglean [--json] [--ci] <evidence.json> [evidence2.json ...]\n\n" ++
  "Options:\n" ++
  "  --json    Emit machine-readable JSON report(s) instead of text reports\n" ++
  "  --ci      Include the conditional independent-marker-set Hoeffding CI in text reports\n" ++
  "  --help    Show this usage message\n"

def processFile (jsonMode showCI : Bool) (path : System.FilePath) : IO UInt32 := do
  let rawBytes ← try
    IO.FS.readBinFile path
  catch e =>
    IO.eprintln s!"Error reading '{path}': {e}"
    return 2
  let sha := MAGLean.Sha256.sha256Bytes rawBytes
  let text ← match String.fromUTF8? rawBytes with
    | some s => pure s
    | none =>
      IO.eprintln s!"Error decoding '{path}' as UTF-8"
      return 2
  let prov : ReportProvenance := {
    inputSha256 := sha
    magleanVersion := magleanVersion
    gitCommit := buildGitCommit
    leanToolchain := Lean.versionString
  }
  match parseMAGEvidence text with
  | .error e =>
    IO.eprintln s!"Parse error in '{path}': {e}"
    return 2
  | .ok ev =>
    match auditMAG ev prov with
    | .error e =>
      IO.eprintln s!"Audit precondition error in '{path}': {e}"
      return 2
    | .ok cert =>
      if jsonMode then
        IO.println (renderJson cert).pretty
      else
        IO.println (renderReport cert showCI)
      return 0

def main (args : List String) : IO UInt32 := do
  let rec parseArgs (jsonMode showCI : Bool) (files : List String) :
      List String → IO (Option (Bool × Bool × List String))
    | [] => pure (some (jsonMode, showCI, files.reverse))
    | "--help" :: _ | "-h" :: _ => do
      IO.println usage
      pure none
    | "--json" :: rest => parseArgs true showCI files rest
    | "--ci" :: rest => parseArgs jsonMode true files rest
    | path :: rest => parseArgs jsonMode showCI (path :: files) rest
  match ← parseArgs false false [] args with
  | none => return 0
  | some (_, _, []) => do
    IO.eprintln usage
    return 1
  | some (jsonMode, showCI, files) => do
    let mut exitCode : UInt32 := 0
    for f in files do
      let rc ← processFile jsonMode showCI f
      if rc != 0 then exitCode := rc
    return exitCode
