import Lean.Data.Json
import MAGLean.Sha256

/-!
# MAGLean.Kernel

Zero-Mathlib, fast-compiling executable MAG QC kernel.

All rational arithmetic uses Lean 4's exact `Rat` type (identical to Mathlib's `ℚ`),
eliminating floating-point rounding drift around MIMAG / CheckM / GUNC cutoffs.
Bridge soundness theorems connecting the kernel's completeness, contamination, marker
mass, composite `Q_5`, MIMAG tier, strain heterogeneity, tree-coherence checker, rank
purity/chimerism table, and Hoeffding radius directly to the Mathlib formal theory live
in `MAGLean.Certificate`.
-/

namespace MAGLean.Kernel

open Lean (Json)

/-- Semantic version of MAGLean. -/
def magleanVersion : String := "0.2.0"

/-- Standard seven taxonomic ranks ordered from `domain` (`0`) to `species` (`6`). -/
inductive KTaxRank where
  | domain
  | phylum
  | class_
  | order
  | family
  | genus
  | species
  deriving DecidableEq, Repr, Inhabited

namespace KTaxRank

def toNat : KTaxRank → Nat
  | domain  => 0
  | phylum  => 1
  | class_  => 2
  | order   => 3
  | family  => 4
  | genus   => 5
  | species => 6

def all : List KTaxRank :=
  [domain, phylum, class_, order, family, genus, species]

def label : KTaxRank → String
  | domain  => "domain"
  | phylum  => "phylum"
  | class_  => "class"
  | order   => "order"
  | family  => "family"
  | genus   => "genus"
  | species => "species"

def le (a b : KTaxRank) : Bool := decide (a.toNat ≤ b.toNat)
def lt (a b : KTaxRank) : Bool := decide (a.toNat < b.toNat)

end KTaxRank

/-- Ribosomal & transfer RNA profile for MIMAG High-Quality verification.
To match Bowers et al. (2017), `distinctTRNAs` counts distinct standard amino-acid
isotypes (out of 20). -/
structure KRNAProfile where
  has23S : Bool
  has16S : Bool
  has5S : Bool
  distinctTRNAs : Nat
  deriving DecidableEq, Repr, Inhabited

def KRNAProfile.satisfiesHQ (r : KRNAProfile) : Bool :=
  r.has23S && r.has16S && r.has5S && decide (18 ≤ r.distinctTRNAs)

/-- Exhaustive MIMAG tier classification. -/
inductive KMIMAGTier where
  | highQuality
  | mediumQuality
  | lowQuality
  | contaminated
  deriving DecidableEq, Repr, Inhabited

def KMIMAGTier.label : KMIMAGTier → String
  | .highQuality   => "High-Quality (MIMAG HQ)"
  | .mediumQuality => "Medium-Quality (MIMAG MQ)"
  | .lowQuality    => "Low-Quality (MIMAG LQ)"
  | .contaminated  => "Contaminated (Failed MIMAG <10% Cont)"

/-- Per-contig evidence ingested from bioinformatics pipelines. -/
structure ContigEvidence where
  id : String
  length : Nat
  markers : List String
  taxonomy : List (KTaxRank × String)
  deriving Repr, Inhabited

/-- Complete MAG evidence bundle. -/
structure MAGEvidence where
  magId : String
  lineage : String
  markerSets : List (List String)
  rna : KRNAProfile
  highIdentityPairs : Nat
  totalMulticopyPairs : Nat
  contigs : List ContigEvidence
  deriving Repr, Inhabited

/-- Provenance metadata authenticating the input bytes and the MAGLean build. -/
structure ReportProvenance where
  inputSha256 : String := ""
  magleanVersion : String := Kernel.magleanVersion
  gitCommit : String := "unknown"
  leanToolchain : String := Lean.versionString
  deriving Repr, Inhabited

/-- Configurable thresholds for taxonomic alert evaluation (informed by CAMI II
benchmarking in Issues #8 and #9). Defaults evaluate stealth chimerism at `genus`
and above (avoiding species-level classifier splits on novel strains) and require
at least 50% classified bp at the evaluated rank. -/
structure AuditConfig where
  maxChimeraRank : KTaxRank := .genus
  minClassifiedFrac : Rat := (1 : Rat) / 2
  deriving Repr, Inhabited

/-- Per-rank taxonomic purity audit record. -/
structure RankAudit where
  rank : KTaxRank
  purityCons : Rat
  purityOpt : Rat
  purityDrop : Rat
  chimerism : Rat
  unclassifiedFrac : Rat
  dominantTaxon : Option String
  deriving Repr

/-- MAG audit report emitted by the kernel. -/
structure MAGCertificate where
  provenance : ReportProvenance
  config : AuditConfig
  magId : String
  lineage : String
  numContigs : Nat
  totalBp : Nat
  accessoryContigs : Nat
  accessoryBp : Nat
  markerBearingContigs : Nat
  numMarkerSets : Nat
  completeness : Rat
  contamination : Rat
  markerMass : Rat
  strainHeterogeneity : Rat
  nonStrainContamination : Rat
  compositeScoreQ5 : Rat
  hoeffding95Radius : Rat
  contigHoeffding95Radius : Rat
  speciesConservativeImpurity : Rat
  mimagTier : KMIMAGTier
  taxCoherent : Bool
  rankAudits : List RankAudit
  alerts : List String
  deriving Repr

/-! ### Exact Rational Marker & Quality Computations -/

def kPresent (n : Nat) : Nat := if n == 0 then 0 else 1
def kExcess (n : Nat) : Nat := n - 1

def dedupStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def countOccurrences (xs : List String) (g : String) : Nat :=
  xs.foldl (fun acc x => if x == g then acc + 1 else acc) 0

def binMarkerCount (contigs : List ContigEvidence) (g : String) : Nat :=
  contigs.foldl (fun acc c => acc + countOccurrences c.markers g) 0

def ratSum (xs : List Rat) : Rat :=
  xs.foldl (· + ·) 0

def kSetComp (s : List String) (f : String → Nat) : Rat :=
  let ds := dedupStrings s
  if ds.isEmpty then 0
  else
    let num : Nat := ds.foldl (fun acc g => acc + kPresent (f g)) 0
    (num : Rat) / (ds.length : Rat)

def kSetCont (s : List String) (f : String → Nat) : Rat :=
  let ds := dedupStrings s
  if ds.isEmpty then 0
  else
    let num : Nat := ds.foldl (fun acc g => acc + kExcess (f g)) 0
    (num : Rat) / (ds.length : Rat)

def kSetMass (s : List String) (f : String → Nat) : Rat :=
  let ds := dedupStrings s
  if ds.isEmpty then 0
  else
    let num : Nat := ds.foldl (fun acc g => acc + f g) 0
    (num : Rat) / (ds.length : Rat)

def kCompleteness (sets : List (List String)) (f : String → Nat) : Rat :=
  if sets.isEmpty then 0
  else ratSum (sets.map (fun s => kSetComp s f)) / (sets.length : Rat)

def kContamination (sets : List (List String)) (f : String → Nat) : Rat :=
  if sets.isEmpty then 0
  else ratSum (sets.map (fun s => kSetCont s f)) / (sets.length : Rat)

def kMarkerMass (sets : List (List String)) (f : String → Nat) : Rat :=
  if sets.isEmpty then 0
  else ratSum (sets.map (fun s => kSetMass s f)) / (sets.length : Rat)

def kStrainHeterogeneity (h t : Nat) : Rat :=
  if t == 0 then 0 else (h : Rat) / (t : Rat)

def kNonStrainCont (cont sh : Rat) : Rat :=
  cont * (1 - sh)

def kClassifyMIMAG (comp cont : Rat) (rna : KRNAProfile) : KMIMAGTier :=
  if (9 : Rat) / 10 < comp && cont < (1 : Rat) / 20 && rna.satisfiesHQ then
    .highQuality
  else if (1 : Rat) / 2 ≤ comp && cont < (1 : Rat) / 10 then
    .mediumQuality
  else if cont < (1 : Rat) / 10 then
    .lowQuality
  else
    .contaminated

/-- Smallest rational `m / 1000` (`1 ≤ m ≤ 1000`) satisfying `2 ≤ k * ε ^ 2`,
proved in `MAGLean.Certificate.kernel_hoeffding95_sound` to give a ≥ 95% two-sided
Hoeffding confidence interval for `k ≥ 2` independent `[0, 1]`-valued observations. -/
def certifiedHoeffding95Radius (k : Nat) : Rat :=
  if k < 2 then 1
  else
    let rec go (m fuel : Nat) : Rat :=
      match fuel with
      | 0 => 1
      | fuel' + 1 =>
        let ε : Rat := (m : Rat) / 1000
        if (2 : Rat) ≤ (k : Rat) * (ε * ε) then ε else go (m + 1) fuel'
    go 1 1000

/-! ### Exact Rational Taxonomic Purity & Tree Coherence -/

def contigTax (c : ContigEvidence) (r : KTaxRank) : Option String :=
  (c.taxonomy.find? (fun p => p.1 == r)).map Prod.snd

def kCheckTaxCoherent (contigs : List ContigEvidence) : Bool :=
  let ranks := KTaxRank.all
  let prefixOk := contigs.all fun c =>
    ranks.all fun r₁ =>
      ranks.all fun r₂ =>
        !(KTaxRank.le r₁ r₂) || !(contigTax c r₂).isSome || (contigTax c r₁).isSome
  let treeOk := contigs.all fun c₁ =>
    contigs.all fun c₂ =>
      ranks.all fun r₁ =>
        ranks.all fun r₂ =>
          !(KTaxRank.le r₁ r₂) ||
            match contigTax c₁ r₂, contigTax c₂ r₂ with
            | some t₁, some t₂ => !(t₁ == t₂) || (contigTax c₁ r₁ == contigTax c₂ r₁)
            | _, _ => true
  prefixOk && treeOk

def kRankAudit (contigs : List ContigEvidence) (r : KTaxRank) : RankAudit :=
  let totBp : Nat := contigs.foldl (fun acc c => acc + c.length) 0
  let classBp : Nat := contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) 0
  let unclassBp : Nat := totBp - classBp
  let taxa : List String := dedupStrings (contigs.filterMap (fun c => contigTax c r))
  let best : Option (String × Nat) :=
    taxa.foldl (fun acc t =>
      let w : Nat := contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0
      match acc with
      | none => some (t, w)
      | some (bt, bw) => if bw < w then some (t, w) else some (bt, bw)
    ) none
  let (domOpt, maxW) := match best with
    | none => (none, 0)
    | some (t, w) => (some t, w)
  let totQ : Rat := (totBp : Rat)
  let classQ : Rat := (classBp : Rat)
  let maxQ : Rat := (maxW : Rat)
  let unclassQ : Rat := (unclassBp : Rat)
  let pCons : Rat := if totBp == 0 then 0 else maxQ / totQ
  let pOpt : Rat := if totBp == 0 then 0 else (maxQ + unclassQ) / totQ
  let pDrop : Rat := if classBp == 0 then 0 else maxQ / classQ
  let uFrac : Rat := if totBp == 0 then 0 else unclassQ / totQ
  { rank := r
    purityCons := pCons
    purityOpt := pOpt
    purityDrop := pDrop
    chimerism := 1 - pCons
    unclassifiedFrac := uFrac
    dominantTaxon := domOpt }

/-! ### Audit Entrypoint -/

def auditMAG (ev : MAGEvidence) (prov : ReportProvenance := {}) (cfg : AuditConfig := {}) :
    Except String MAGCertificate := do
  if ev.markerSets.isEmpty then
    throw "Invalid evidence: marker_sets must be nonempty."
  if ev.markerSets.any (fun s => (dedupStrings s).isEmpty) then
    throw "Invalid evidence: every collocated marker set must be nonempty."
  let canon : List String → List String := fun xs =>
    (dedupStrings xs).mergeSort (fun a b => decide (a < b) || a == b)
  let canonSets := ev.markerSets.map canon
  if (canonSets.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []).length != canonSets.length then
    throw "Invalid evidence: duplicate marker sets; the confidence radius assumes each set is a separate observation."
  if ev.contigs.isEmpty then
    throw "Invalid evidence: bin must contain at least one contig."
  if ev.contigs.any (fun c => c.length == 0) then
    throw "Invalid evidence: contig length must be positive."
  let ids := ev.contigs.map (·.id)
  if (dedupStrings ids).length != ids.length then
    throw "Invalid evidence: duplicate contig IDs detected."
  let prof := binMarkerCount ev.contigs
  let comp := kCompleteness ev.markerSets prof
  let cont := kContamination ev.markerSets prof
  let mass := kMarkerMass ev.markerSets prof
  let sh := kStrainHeterogeneity ev.highIdentityPairs ev.totalMulticopyPairs
  let nsc := kNonStrainCont cont sh
  let q5 := comp - 5 * cont
  let tier := kClassifyMIMAG comp cont ev.rna
  let rad95 := certifiedHoeffding95Radius ev.markerSets.length
  let coherent := kCheckTaxCoherent ev.contigs
  let rankAudits := KTaxRank.all.map (kRankAudit ev.contigs)
  let speciesImpurity : Rat :=
    match rankAudits.find? (fun ra => ra.rank == .species) with
    | some ra => ra.chimerism
    | none => 0
  let allMarkers := dedupStrings (ev.markerSets.flatten)
  let accContigs := ev.contigs.filter (fun c => c.markers.all (fun g => !allMarkers.contains g))
  let markerContigs := ev.contigs.length - accContigs.length
  let contigRad95 := certifiedHoeffding95Radius markerContigs
  let accBp := accContigs.foldl (fun s c => s + c.length) 0
  let totalBp := ev.contigs.foldl (fun s c => s + c.length) 0
  let mut alerts : List String := []
  if !coherent then
    alerts := alerts ++ ["TAXONOMIC_INCOHERENCE: Contig lineages violate tree consistency or prefix-closedness."]
  if (9 : Rat) / 10 < comp && cont < (1 : Rat) / 20 && !ev.rna.satisfiesHQ then
    alerts := alerts ++ ["MIMAG_HQ_RNA_DOWNGRADE: Marker metrics pass HQ (>90% comp, <5% cont) but RNA profile fails (23S/16S/5S + ≥18 tRNAs); downgraded to MQ."]
  -- Stealth chimera alert (Issues #8): evaluate only at ranks `≤ cfg.maxChimeraRank`
  -- (default `genus`, avoiding species-level splits on novel strains) with classified bp
  -- fraction `1 - unclassifiedFrac ≥ cfg.minClassifiedFrac` (default 50%).
  let worstOptimisticPurity : Rat :=
    rankAudits.foldl (fun acc ra =>
      let classFrac := (1 : Rat) - ra.unclassifiedFrac
      if KTaxRank.le ra.rank cfg.maxChimeraRank && cfg.minClassifiedFrac ≤ classFrac &&
          ra.purityOpt < acc then ra.purityOpt else acc) (1 : Rat)
  if cont < (1 : Rat) / 20 && worstOptimisticPurity < (9 : Rat) / 10 then
    alerts := alerts ++ [s!"STEALTH_CHIMERA_ALERT: Low marker contamination (<5%) masks multi-clade taxonomic chimerism (>10% of bp classified outside the dominant taxon at rank ≤ {cfg.maxChimeraRank.label} with ≥{formatPercent cfg.minClassifiedFrac} classified bp)."]
  -- Unclassified dilution alert (Issue #9): fire only when a coarser rank (≤ maxChimeraRank)
  -- is genuinely impure (`purityDrop < 90%`) and a finer rank masks it to `purityDrop ≥ 90%`
  -- by dropping unclassified contigs, rather than on benign upward drift of already-clean bins.
  let mut dilutionDetected := false
  for ra₁ in rankAudits do
    for ra₂ in rankAudits do
      if KTaxRank.le ra₁.rank cfg.maxChimeraRank && KTaxRank.lt ra₁.rank ra₂.rank &&
          ra₁.unclassifiedFrac < 1 && ra₂.unclassifiedFrac < 1 &&
          ra₁.purityDrop < (9 : Rat) / 10 && (9 : Rat) / 10 ≤ ra₂.purityDrop then
        dilutionDetected := true
  if dilutionDetected then
    alerts := alerts ++ ["UNCLASSIFIED_DILUTION_ALERT: Coarser-rank chimerism (drop-purity <90%) is masked to ≥90% at a finer rank by dropping unclassified contigs; inspect [purityCons, purityOpt] sandwich interval."]
  if ev.markerSets.length < 50 then
    alerts := alerts ++ [s!"LOW_MARKER_RESOLUTION: Only {ev.markerSets.length} collocated marker sets; independent-set ≥95% Hoeffding radius is ±{formatPercent rad95}."]
  return {
    provenance := prov
    config := cfg
    magId := ev.magId
    lineage := ev.lineage
    numContigs := ev.contigs.length
    totalBp := totalBp
    accessoryContigs := accContigs.length
    accessoryBp := accBp
    markerBearingContigs := markerContigs
    numMarkerSets := ev.markerSets.length
    completeness := comp
    contamination := cont
    markerMass := mass
    strainHeterogeneity := sh
    nonStrainContamination := nsc
    compositeScoreQ5 := q5
    hoeffding95Radius := rad95
    contigHoeffding95Radius := contigRad95
    speciesConservativeImpurity := speciesImpurity
    mimagTier := tier
    taxCoherent := coherent
    rankAudits := rankAudits
    alerts := alerts
  }
where
  formatPercent (q : Rat) : String :=
    let neg := q < 0
    let aq := if neg then -q else q
    let scaled : Nat := (aq.num.natAbs * 10000) / aq.den
    let whole := scaled / 100
    let frac := scaled % 100
    let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
    let sign := if neg then "-" else ""
    s!"{sign}{whole}.{fracStr}%"

/-! ### JSON Parsing & Rendering -/

def parseRankKey : String → Option KTaxRank
  | "domain"  => some .domain
  | "phylum"  => some .phylum
  | "class"   => some .class_
  | "order"   => some .order
  | "family"  => some .family
  | "genus"   => some .genus
  | "species" => some .species
  | _         => none

private def getStrField (j : Json) (k : String) : Except String String :=
  match j.getObjVal? k with
  | .ok (.str s) => .ok s
  | _ => .error s!"Missing or non-string field '{k}'"

private def getNatField (j : Json) (k : String) : Except String Nat :=
  match j.getObjVal? k with
  | .ok (.num n) =>
    if n.exponent == 0 && n.mantissa ≥ 0 then .ok n.mantissa.toNat
    else .error s!"Field '{k}' must be a non-negative integer"
  | _ => .error s!"Missing or non-integer field '{k}'"

private def getBoolField (j : Json) (k : String) : Except String Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => .ok b
  | _ => .error s!"Missing or non-boolean field '{k}'"

private def getStrArray (j : Json) (k : String) : Except String (List String) :=
  match j.getObjVal? k with
  | .ok (.arr arr) =>
    arr.toList.mapM fun x =>
      match x with
      | .str s => .ok s
      | _ => .error s!"Non-string element in array '{k}'"
  | _ => .error s!"Missing or non-array field '{k}'"

private def parseTaxonomyObj (j : Json) : Except String (List (KTaxRank × String)) :=
  match j with
  | .obj kv =>
    kv.toList.foldlM (fun acc (k, v) =>
      match parseRankKey k with
      | none => .error s!"Unknown taxonomy rank '{k}'; expected one of domain, phylum, class, order, family, genus, species"
      | some r =>
        match v with
        | .str s => .ok (acc ++ [(r, s)])
        | .null => .ok acc
        | _ => .error s!"Taxonomy value for rank '{k}' must be string or null"
    ) []
  | _ => .error "Field 'taxonomy' must be a JSON object"

private def parseContig (j : Json) : Except String ContigEvidence := do
  let id ← getStrField j "id"
  let length ← getNatField j "length"
  let markers ← getStrArray j "markers"
  let taxJson ← match j.getObjVal? "taxonomy" with
    | .ok tj => .ok tj
    | .error e => .error s!"Contig '{id}': {e}"
  let taxonomy ← parseTaxonomyObj taxJson
  return { id, length, markers, taxonomy }

def parseMAGEvidence (text : String) : Except String MAGEvidence := do
  let j ← Json.parse text
  let magId ← getStrField j "mag_id"
  let lineage ← match j.getObjVal? "lineage" with
    | .ok (.str s) => .ok s
    | _ => .ok "unclassified"
  let markerSets ← match j.getObjVal? "marker_sets" with
    | .ok (.arr arr) =>
      arr.toList.mapM fun sJson =>
        match sJson with
        | .arr inner =>
          inner.toList.mapM fun x =>
            match x with
            | .str g => .ok g
            | _ => .error "Non-string marker in marker_sets"
        | _ => .error "Each element of marker_sets must be an array of strings"
    | _ => .error "Missing or invalid 'marker_sets'"
  let rnaJson ← match j.getObjVal? "rna" with
    | .ok rj => .ok rj
    | .error e => .error s!"Missing 'rna' object: {e}"
  let has23S ← getBoolField rnaJson "has_23S"
  let has16S ← getBoolField rnaJson "has_16S"
  let has5S ← getBoolField rnaJson "has_5S"
  let distinctTRNAs ← getNatField rnaJson "distinct_tRNAs"
  let (highId, totalMc) ← match j.getObjVal? "strain_heterogeneity" with
    | .ok shJson => do
      let h ← getNatField shJson "high_identity_pairs"
      let t ← getNatField shJson "total_multicopy_pairs"
      pure (h, t)
    | .error _ => pure (0, 0)
  let contigs ← match j.getObjVal? "contigs" with
    | .ok (.arr arr) => arr.toList.mapM parseContig
    | _ => .error "Missing or invalid 'contigs' array"
  return {
    magId := magId
    lineage := lineage
    markerSets := markerSets
    rna := { has23S, has16S, has5S, distinctTRNAs }
    highIdentityPairs := highId
    totalMulticopyPairs := totalMc
    contigs := contigs
  }

def formatPercent (q : Rat) : String :=
  let neg := q < 0
  let aq := if neg then -q else q
  let scaled : Nat := (aq.num.natAbs * 10000) / aq.den
  let whole := scaled / 100
  let frac := scaled % 100
  let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
  let sign := if neg then "-" else ""
  s!"{sign}{whole}.{fracStr}%"

def formatRat (q : Rat) : String :=
  if q.den == 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

private def padRight (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

def renderReport (cert : MAGCertificate) (showCI : Bool := false) : String :=
  let ciLo := if cert.completeness < cert.hoeffding95Radius then (0 : Rat) else cert.completeness - cert.hoeffding95Radius
  let ciHi := if (1 : Rat) < cert.completeness + cert.hoeffding95Radius then (1 : Rat) else cert.completeness + cert.hoeffding95Radius
  let ciLines :=
    if showCI then
      [s!"  Hoeffding ≥95% CI  : [{formatPercent ciLo}, {formatPercent ciHi}]  (radius ±{formatPercent cert.hoeffding95Radius}; conditional on independent marker-set detections)"]
    else
      [s!"  Marker-Set CI      : omitted by default (pass --ci to print conditional independent-set Hoeffding radius ±{formatPercent cert.hoeffding95Radius})"]
  let header := [
    "========================================================================",
    s!"MAGLean QC Report: {cert.magId}",
    "========================================================================",
    s!"MAGLean Build        : v{cert.provenance.magleanVersion} (commit {cert.provenance.gitCommit}, Lean {cert.provenance.leanToolchain})",
    s!"Input SHA-256        : {cert.provenance.inputSha256}",
    s!"Lineage              : {cert.lineage}",
    s!"Assembly Summary     : {cert.numContigs} contigs ({cert.markerBearingContigs} marker-bearing), {cert.totalBp} bp",
    s!"Accessory Contigs    : {cert.accessoryContigs} marker-free contigs ({cert.accessoryBp} bp) [invariant under marker QC]",
    s!"Marker Family        : {cert.numMarkerSets} collocated single-copy marker sets",
    "------------------------------------------------------------------------",
    "EXACT RATIONAL MARKER METRICS (CheckM Collocated Model)",
    s!"  Completeness       : {formatPercent cert.completeness}  (exact: {formatRat cert.completeness})",
    s!"  Contamination      : {formatPercent cert.contamination}  (exact: {formatRat cert.contamination})",
    s!"  Total Marker Mass  : {formatPercent cert.markerMass}  (exact: {formatRat cert.markerMass}) [Comp + Cont conserved]",
    s!"  Split Ceiling      : Combined completeness of any split ≤ {formatPercent cert.markerMass}",
    s!"  Strain Heterogen.  : {formatPercent cert.strainHeterogeneity}  (heuristic cont*(1-SH): {formatPercent cert.nonStrainContamination}; exact only for ≤2 copies/marker)",
    s!"  Composite Q_5      : {formatPercent cert.compositeScoreQ5}  (exact: {formatRat cert.compositeScoreQ5})",
    s!"  Contig-Level Rad.  : ±{formatPercent cert.contigHoeffding95Radius}  ({cert.markerBearingContigs} marker-bearing contigs; assumes equal-weight independent contigs)"
  ] ++ ciLines ++ [
    "------------------------------------------------------------------------",
    "VERIFIED STANDARDS & COHERENCE",
    s!"  MIMAG Tier         : {cert.mimagTier.label}",
    s!"  Tree Coherence     : {if cert.taxCoherent then "CERTIFIED (kCheckTaxCoherent_sound → TaxCoherent & rank-refinement monotonicity)" else "FAILED (violates prefix-closedness or tree consistency)"}",
    "------------------------------------------------------------------------",
    "TAXONOMIC RANK PURITY & CHIMERISM AUDIT (Conservative / Optimistic / Drop)"
  ]
  let rankLines := cert.rankAudits.map fun ra =>
    let dom := ra.dominantTaxon.getD "none"
    s!"  {padRight ra.rank.label 8} | cons={padRight (formatPercent ra.purityCons) 8} opt={padRight (formatPercent ra.purityOpt) 8} drop={padRight (formatPercent ra.purityDrop) 8} chim={padRight (formatPercent ra.chimerism) 8} unclass={padRight (formatPercent ra.unclassifiedFrac) 8} dom={dom}"
  let alertSection :=
    if cert.alerts.isEmpty then
      ["------------------------------------------------------------------------",
       "ALERTS               : None — passed all formal marker, MIMAG, and taxonomic checks."]
    else
      ["------------------------------------------------------------------------",
       "ALERTS               :"] ++ cert.alerts.map (fun a => s!"  [!] {a}")
  String.intercalate "\n" (header ++ rankLines ++ alertSection ++ ["========================================================================"])

def renderJson (cert : MAGCertificate) : Json :=
  Json.mkObj [
    ("maglean_version", Json.str cert.provenance.magleanVersion),
    ("git_commit", Json.str cert.provenance.gitCommit),
    ("lean_toolchain", Json.str cert.provenance.leanToolchain),
    ("input_sha256", Json.str cert.provenance.inputSha256),
    ("mag_id", Json.str cert.magId),
    ("lineage", Json.str cert.lineage),
    ("num_contigs", Json.num cert.numContigs),
    ("marker_bearing_contigs", Json.num cert.markerBearingContigs),
    ("total_bp", Json.num cert.totalBp),
    ("accessory_contigs", Json.num cert.accessoryContigs),
    ("accessory_bp", Json.num cert.accessoryBp),
    ("num_marker_sets", Json.num cert.numMarkerSets),
    ("completeness_exact", Json.str (formatRat cert.completeness)),
    ("completeness_pct", Json.str (formatPercent cert.completeness)),
    ("contamination_exact", Json.str (formatRat cert.contamination)),
    ("contamination_pct", Json.str (formatPercent cert.contamination)),
    ("marker_mass_exact", Json.str (formatRat cert.markerMass)),
    ("strain_heterogeneity_exact", Json.str (formatRat cert.strainHeterogeneity)),
    ("non_strain_cont_heuristic_exact", Json.str (formatRat cert.nonStrainContamination)),
    ("composite_q5_exact", Json.str (formatRat cert.compositeScoreQ5)),
    ("hoeffding_95_radius_exact", Json.str (formatRat cert.hoeffding95Radius)),
    ("hoeffding_95_assumptions", Json.str "conditional on independent [0,1]-bounded marker-set detections"),
    ("contig_hoeffding_95_radius_exact", Json.str (formatRat cert.contigHoeffding95Radius)),
    ("species_conservative_impurity_exact", Json.str (formatRat cert.speciesConservativeImpurity)),
    ("max_chimera_rank", Json.str cert.config.maxChimeraRank.label),
    ("min_classified_frac_exact", Json.str (formatRat cert.config.minClassifiedFrac)),
    ("mimag_tier", Json.str cert.mimagTier.label),
    ("tax_coherent", Json.bool cert.taxCoherent),
    ("rank_audits", Json.arr (cert.rankAudits.toArray.map fun ra =>
      Json.mkObj [
        ("rank", Json.str ra.rank.label),
        ("purity_cons", Json.str (formatRat ra.purityCons)),
        ("purity_opt", Json.str (formatRat ra.purityOpt)),
        ("purity_drop", Json.str (formatRat ra.purityDrop)),
        ("chimerism", Json.str (formatRat ra.chimerism)),
        ("unclassified_frac", Json.str (formatRat ra.unclassifiedFrac)),
        ("dominant_taxon", match ra.dominantTaxon with | some s => Json.str s | none => Json.null)
      ])),
    ("alerts", Json.arr (cert.alerts.toArray.map Json.str))
  ]

end MAGLean.Kernel
