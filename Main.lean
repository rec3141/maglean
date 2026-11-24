import MAGLean.Kernel
import MAGLean.BuildInfo

open MAGLean.Kernel

def usage : String :=
  "MAGLean — Quality Control Auditor for Metagenome-Assembled Genomes\n\n" ++
  "Usage:\n" ++
  "  maglean [options] <evidence.json> [evidence2.json ...]\n\n" ++
  "Options:\n" ++
  "  --json                        Emit machine-readable JSON report(s)\n" ++
  "  --ci                          Include conditional independent-marker-set Hoeffding CI in text reports\n" ++
  "  --max-chimera-rank <rank>     Finest rank checked for STEALTH_CHIMERA_ALERT (default: genus)\n" ++
  "  --min-classified-pct <0..100> Minimum classified bp % for taxonomic alerts (default: 50)\n" ++
  "  --help                        Show this usage message\n"

def processFile (jsonMode showCI : Bool) (cfg : AuditConfig) (path : System.FilePath) : IO UInt32 := do
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
    gitCommit := MAGLean.BuildInfo.gitCommit
    leanToolchain := Lean.versionString
  }
  match parseMAGEvidence text with
  | .error e =>
    IO.eprintln s!"Parse error in '{path}': {e}"
    return 2
  | .ok ev =>
    match auditMAG ev prov cfg with
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
  let rec parseArgs (jsonMode showCI : Bool) (cfg : AuditConfig) (files : List String) :
      List String → IO (Except UInt32 (Bool × Bool × AuditConfig × List String))
    | [] => pure (.ok (jsonMode, showCI, cfg, files.reverse))
    | "--help" :: _ | "-h" :: _ => do
      IO.println usage
      pure (.error 0)
    | "--json" :: rest => parseArgs true showCI cfg files rest
    | "--ci" :: rest => parseArgs jsonMode true cfg files rest
    | "--max-chimera-rank" :: rStr :: rest =>
      match parseRankKey rStr with
      | some rk => parseArgs jsonMode showCI { cfg with maxChimeraRank := rk } files rest
      | none => do
        IO.eprintln s!"Invalid --max-chimera-rank '{rStr}'; expected domain|phylum|class|order|family|genus|species"
        pure (.error 2)
    | "--min-classified-pct" :: pStr :: rest =>
      match pStr.toNat? with
      | some p =>
        if p ≤ 100 then
          parseArgs jsonMode showCI { cfg with minClassifiedFrac := (p : Rat) / 100 } files rest
        else do
          IO.eprintln s!"Invalid --min-classified-pct '{pStr}'; expected integer 0..100"
          pure (.error 2)
      | none => do
        IO.eprintln s!"Invalid --min-classified-pct '{pStr}'; expected integer 0..100"
        pure (.error 2)
    | path :: rest => parseArgs jsonMode showCI cfg (path :: files) rest
  match ← parseArgs false false {} [] args with
  | .error code => return code
  | .ok (_, _, _, []) => do
    IO.eprintln usage
    return 1
  | .ok (jsonMode, showCI, cfg, files) => do
    let mut exitCode : UInt32 := 0
    for f in files do
      let rc ← processFile jsonMode showCI cfg f
      if rc != 0 then exitCode := rc
    return exitCode
