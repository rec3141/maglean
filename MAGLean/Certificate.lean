import MAGLean.Kernel
import MAGLean.Markers
import MAGLean.Probabilistic
import MAGLean.Taxonomy
import MAGLean.Quality
import MAGLean.Dereplication
import MAGLean.Binning
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# MAGLean.Certificate

Machine-checked soundness bridge between the fast, zero-Mathlib executable kernel
(`MAGLean.Kernel`, compiled into the native `maglean` CLI binary) and the full
Mathlib formalization (`MAGLean.Markers`, `MAGLean.Probabilistic`, `MAGLean.Taxonomy`,
`MAGLean.Quality`, `MAGLean.Dereplication`, `MAGLean.Binning`).

## Main Soundness & Equivalence Theorems

* `kCompleteness_eq_completeness`, `kContamination_eq_contamination`,
  `kMarkerMass_eq_markerMass`, `kCompositeQ5_eq_compositeScore`,
  `binMarkerCount_eq_binCounts`: Exact equality between the executable CLI's marker
  metrics and the Mathlib `Markers` / `Quality` definitions.
* `kCompleteness_add_kContamination_eq_kMarkerMass`: Exact rational conservation law
  directly on the kernel functions.
* `kClassifyMIMAG_eq_classifyMIMAG`: Exact agreement with `Quality.classifyMIMAG`.
* `kStrainHeterogeneity_eq`, `kNonStrainCont_eq`: Exact agreement with `Markers`.
* `kCheckTaxCoherent_sound`: Directly proves that when `Kernel.kCheckTaxCoherent contigs = true`
  (with unique contig IDs), the bin satisfies `Taxonomy.TaxCoherent`, unlocking
  `Taxonomy.rank_refinement_monotonicity`.
* `kRankAudit_purityCons_eq`, `kRankAudit_purityOpt_eq`, `kRankAudit_purityDrop_eq`,
  `kRankAudit_chimerism_eq`, `kRankAudit_unclassifiedFrac_eq`,
  `kRankAudit_stealth_alert_sound`: Exact equality between `Kernel.kRankAudit` (the CLI's
  per-rank purity/chimerism table and stealth-chimera alert condition) and the
  `Taxonomy` definitions and `purity_unclassified_sandwich` theorem.
* `hoeffding95_cert_sound` & `kernel_hoeffding95_sound`: For every `k ≥ 2`, the rational
  radius `ε = Kernel.certifiedHoeffding95Radius k` provably certifies a ≥ 95% two-sided
  Hoeffding bound under the independent observation model.
-/

namespace MAGLean.Certificate

open MAGLean.Kernel
open MAGLean.Taxonomy
open MAGLean.Quality

/-! ### Type Isomorphisms Between Kernel and Theory -/

def toTaxRank : KTaxRank → TaxRank
  | .domain  => .domain
  | .phylum  => .phylum
  | .class_  => .class_
  | .order   => .order
  | .family  => .family
  | .genus   => .genus
  | .species => .species

def fromTaxRank : TaxRank → KTaxRank
  | .domain  => .domain
  | .phylum  => .phylum
  | .class_  => .class_
  | .order   => .order
  | .family  => .family
  | .genus   => .genus
  | .species => .species

@[simp] lemma fromTaxRank_toTaxRank (r : KTaxRank) : fromTaxRank (toTaxRank r) = r := by
  cases r <;> rfl

@[simp] lemma toTaxRank_fromTaxRank (r : TaxRank) : toTaxRank (fromTaxRank r) = r := by
  cases r <;> rfl

lemma toTaxRank_toNat (r : KTaxRank) : (toTaxRank r).toNat = r.toNat := by
  cases r <;> rfl

lemma kTaxRank_le_iff (r₁ r₂ : KTaxRank) :
    KTaxRank.le r₁ r₂ = true ↔ toTaxRank r₁ ≤ toTaxRank r₂ := by
  unfold KTaxRank.le
  rw [TaxRank.le_iff_toNat_le, toTaxRank_toNat, toTaxRank_toNat, decide_eq_true_eq]

lemma mem_kTaxRank_all (r : KTaxRank) : r ∈ KTaxRank.all := by
  cases r <;> simp [KTaxRank.all]

def toRNAProfile (r : KRNAProfile) : RNAProfile :=
  { has23S := r.has23S
    has16S := r.has16S
    has5S := r.has5S
    distinctTRNAs := r.distinctTRNAs }

def toMIMAGTier : KMIMAGTier → MIMAGTier
  | .highQuality   => .highQuality
  | .mediumQuality => .mediumQuality
  | .lowQuality    => .lowQuality
  | .contaminated  => .contaminated

/-! ### List / Fold / Dedup Bridge Lemmas -/

theorem kPresent_eq_present (n : ℕ) : kPresent n = present n := by
  cases n <;> rfl

theorem kExcess_eq_excess (n : ℕ) : kExcess n = excess n := rfl

private lemma foldl_add_nat {β : Type*} (l : List β) (g : β → ℕ) (init : ℕ) :
    l.foldl (fun acc x => acc + g x) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

private lemma ratSum_eq_sum (xs : List ℚ) : ratSum xs = xs.sum := by
  unfold ratSum
  suffices ∀ init : ℚ, xs.foldl (· + ·) init = init + xs.sum by
    simpa using this 0
  induction xs with
  | nil => intro init; simp
  | cons x rest ih =>
    intro init
    simp only [List.foldl_cons, List.sum_cons, ih]
    ring

private lemma list_sum_map_add_nat {β : Type*} (l : List β) (u v : β → ℕ) :
    (l.map (fun x => u x + v x)).sum = (l.map u).sum + (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private lemma list_sum_map_add_rat {β : Type*} (l : List β) (u v : β → ℚ) :
    (l.map (fun x => u x + v x)).sum = (l.map u).sum + (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma mem_foldl_dedup (xs acc : List String) (y : String) :
    y ∈ xs.foldl (fun a x => if a.contains x then a else a ++ [x]) acc ↔ y ∈ acc ∨ y ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    split_ifs with hcont
    · have hx : x ∈ acc := List.elem_iff.mp hcont
      constructor
      · rintro (ha | hr)
        · left; exact ha
        · right; right; exact hr
      · rintro (ha | rfl | hr)
        · left; exact ha
        · left; exact hx
        · right; exact hr
    · simp only [List.mem_append, List.mem_singleton]
      tauto

private lemma nodup_foldl_dedup (xs acc : List String) (hacc : acc.Nodup) :
    (xs.foldl (fun a x => if a.contains x then a else a ++ [x]) acc).Nodup := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x rest ih =>
    simp only [List.foldl_cons]
    split_ifs with hcont
    · exact ih acc hacc
    · apply ih
      rw [List.nodup_append]
      refine ⟨hacc, List.nodup_singleton x, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hcont (List.elem_iff.mpr ha)

lemma mem_dedupStrings (xs : List String) (y : String) :
    y ∈ dedupStrings xs ↔ y ∈ xs := by
  unfold dedupStrings
  simpa using mem_foldl_dedup xs [] y

lemma dedupStrings_nodup (xs : List String) : (dedupStrings xs).Nodup :=
  nodup_foldl_dedup xs [] List.nodup_nil

lemma dedupStrings_toFinset (xs : List String) : (dedupStrings xs).toFinset = xs.toFinset := by
  ext y
  simp [List.mem_toFinset, mem_dedupStrings]

lemma dedupStrings_length (xs : List String) : (dedupStrings xs).length = xs.toFinset.card := by
  rw [← dedupStrings_toFinset, List.toFinset_card_of_nodup (dedupStrings_nodup xs)]

lemma dedupStrings_sum_nat (xs : List String) (g : String → ℕ) :
    ((dedupStrings xs).map g).sum = ∑ y ∈ xs.toFinset, g y := by
  rw [← dedupStrings_toFinset]
  exact (List.sum_toFinset g (dedupStrings_nodup xs)).symm

/-! ### Bridge Theorems: Kernel Marker Metrics = `MAGLean.Markers` -/

theorem kSetComp_eq_setComp (s : List String) (f : String → ℕ) :
    kSetComp s f = setComp s.toFinset f := by
  unfold kSetComp setComp
  dsimp only
  split_ifs with hemp
  · have hlen : (dedupStrings s).length = 0 := List.isEmpty_iff_length_eq_zero.mp hemp
    have hcard : s.toFinset.card = 0 := by rw [← dedupStrings_length, hlen]
    simp [hcard]
  · rw [foldl_add_nat, Nat.zero_add, dedupStrings_length]
    have hsum : ((dedupStrings s).map (fun g => kPresent (f g))).sum =
        ∑ g ∈ s.toFinset, present (f g) := by
      have hcongr : (dedupStrings s).map (fun g => kPresent (f g)) =
          (dedupStrings s).map (fun g => present (f g)) :=
        List.map_congr_left (fun g _ => kPresent_eq_present (f g))
      rw [hcongr, dedupStrings_sum_nat]
    rw [hsum, Nat.cast_sum]

theorem kSetCont_eq_setCont (s : List String) (f : String → ℕ) :
    kSetCont s f = setCont s.toFinset f := by
  unfold kSetCont setCont
  dsimp only
  split_ifs with hemp
  · have hlen : (dedupStrings s).length = 0 := List.isEmpty_iff_length_eq_zero.mp hemp
    have hcard : s.toFinset.card = 0 := by rw [← dedupStrings_length, hlen]
    simp [hcard]
  · rw [foldl_add_nat, Nat.zero_add, dedupStrings_length]
    have hsum : ((dedupStrings s).map (fun g => kExcess (f g))).sum =
        ∑ g ∈ s.toFinset, excess (f g) := by
      have hcongr : (dedupStrings s).map (fun g => kExcess (f g)) =
          (dedupStrings s).map (fun g => excess (f g)) :=
        List.map_congr_left (fun g _ => kExcess_eq_excess (f g))
      rw [hcongr, dedupStrings_sum_nat]
    rw [hsum, Nat.cast_sum]

theorem kSetMass_eq_setMass (s : List String) (f : String → ℕ) :
    kSetMass s f = setMass s.toFinset f := by
  unfold kSetMass setMass
  dsimp only
  split_ifs with hemp
  · have hlen : (dedupStrings s).length = 0 := List.isEmpty_iff_length_eq_zero.mp hemp
    have hcard : s.toFinset.card = 0 := by rw [← dedupStrings_length, hlen]
    simp [hcard]
  · rw [foldl_add_nat, Nat.zero_add, dedupStrings_length, dedupStrings_sum_nat, Nat.cast_sum]

/-- Construct the Mathlib `MarkerFamily String` corresponding to validated CLI marker sets. -/
def toMarkerFamily (sets : List (List String)) (hne : sets ≠ [])
    (hmem : ∀ s ∈ sets.map List.toFinset, s.Nonempty) : MarkerFamily String :=
  ⟨sets.map List.toFinset, by simp [hne], hmem⟩

/-- **Exact Completeness Bridge**: `Kernel.kCompleteness` equals `Markers.completeness`. -/
theorem kCompleteness_eq_completeness (sets : List (List String)) (hne : sets ≠ [])
    (hmem : ∀ s ∈ sets.map List.toFinset, s.Nonempty) (f : String → ℕ) :
    kCompleteness sets f = completeness (toMarkerFamily sets hne hmem) f := by
  unfold kCompleteness completeness toMarkerFamily MarkerFamily.numSets
  have hne_bool : sets.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [hne_bool, Bool.false_eq_true, ↓reduceIte, List.length_map, ratSum_eq_sum]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  exact kSetComp_eq_setComp s f

/-- **Exact Contamination Bridge**: `Kernel.kContamination` equals `Markers.contamination`. -/
theorem kContamination_eq_contamination (sets : List (List String)) (hne : sets ≠ [])
    (hmem : ∀ s ∈ sets.map List.toFinset, s.Nonempty) (f : String → ℕ) :
    kContamination sets f = contamination (toMarkerFamily sets hne hmem) f := by
  unfold kContamination contamination toMarkerFamily MarkerFamily.numSets
  have hne_bool : sets.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [hne_bool, Bool.false_eq_true, ↓reduceIte, List.length_map, ratSum_eq_sum]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  exact kSetCont_eq_setCont s f

/-- **Exact Marker Mass Bridge**: `Kernel.kMarkerMass` equals `Markers.markerMass`. -/
theorem kMarkerMass_eq_markerMass (sets : List (List String)) (hne : sets ≠ [])
    (hmem : ∀ s ∈ sets.map List.toFinset, s.Nonempty) (f : String → ℕ) :
    kMarkerMass sets f = markerMass (toMarkerFamily sets hne hmem) f := by
  unfold kMarkerMass markerMass toMarkerFamily MarkerFamily.numSets
  have hne_bool : sets.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [hne_bool, Bool.false_eq_true, ↓reduceIte, List.length_map, ratSum_eq_sum]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  exact kSetMass_eq_setMass s f

/-- **Exact Composite `Q_5` Bridge**: The CLI's `comp - 5 * cont` equals `Quality.compositeScore 5`. -/
theorem kCompositeQ5_eq_compositeScore (sets : List (List String)) (hne : sets ≠ [])
    (hmem : ∀ s ∈ sets.map List.toFinset, s.Nonempty) (f : String → ℕ) :
    kCompleteness sets f - 5 * kContamination sets f =
      Quality.compositeScore 5 (toMarkerFamily sets hne hmem) f := by
  unfold Quality.compositeScore
  rw [kCompleteness_eq_completeness sets hne hmem f,
      kContamination_eq_contamination sets hne hmem f]

/-- Per-set conservation law directly on the executable kernel functions. -/
theorem kSetComp_add_kSetCont_eq_kSetMass (s : List String) (f : String → ℕ) :
    kSetComp s f + kSetCont s f = kSetMass s f := by
  rw [kSetComp_eq_setComp, kSetCont_eq_setCont, kSetMass_eq_setMass, setComp_add_setCont]

/-- **Kernel Marker-Mass Conservation Theorem**: For *every* marker family `sets` and
profile `f`, `kCompleteness + kContamination = kMarkerMass` holds identically. -/
theorem kCompleteness_add_kContamination_eq_kMarkerMass
    (sets : List (List String)) (f : String → ℕ) :
    kCompleteness sets f + kContamination sets f = kMarkerMass sets f := by
  unfold kCompleteness kContamination kMarkerMass
  split_ifs with hemp
  · simp
  · rw [ratSum_eq_sum, ratSum_eq_sum, ratSum_eq_sum, ← add_div, ← list_sum_map_add_rat]
    congr 2
    apply List.map_congr_left
    intro s _
    exact kSetComp_add_kSetCont_eq_kSetMass s f

/-! ### Contig-List to Finset Representation & Lookup Lemmas -/

/-- Finset of contig IDs represented by a list of `ContigEvidence`. -/
def contigBin (contigs : List ContigEvidence) : Finset String :=
  (contigs.map (·.id)).toFinset

/-- Contig length lookup by ID. -/
def contigLenOf (contigs : List ContigEvidence) (cid : String) : ℕ :=
  match contigs.find? (fun c => c.id == cid) with
  | some c => c.length
  | none => 0

/-- Contig marker-hit count lookup by ID. -/
def contigHitsOf (contigs : List ContigEvidence) (cid : String) (g : String) : ℕ :=
  match contigs.find? (fun c => c.id == cid) with
  | some c => countOccurrences c.markers g
  | none => 0

/-- Contig taxonomy lookup by ID and `TaxRank`. -/
def contigTaxOf (contigs : List ContigEvidence) (cid : String) (r : TaxRank) : Option String :=
  match contigs.find? (fun c => c.id == cid) with
  | some c => contigTax c (fromTaxRank r)
  | none => none

private lemma find?_eq_some_of_mem_nodup {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) {c : ContigEvidence} (hc : c ∈ contigs) :
    contigs.find? (fun x => x.id == c.id) = some c := by
  induction contigs with
  | nil => simp at hc
  | cons x rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hc with rfl | hmem
    · simp [List.find?]
    · have hne : x.id ≠ c.id := by
        intro heq
        exact hnodup.1 (heq ▸ List.mem_map_of_mem hmem)
      have hbeq : (x.id == c.id) = false := beq_false_of_ne hne
      simp only [List.find?, hbeq]
      exact ih hnodup.2 hmem

lemma mem_contigBin_iff {contigs : List ContigEvidence} {cid : String} :
    cid ∈ contigBin contigs ↔ ∃ c ∈ contigs, c.id = cid := by
  simp [contigBin, List.mem_toFinset]

private lemma foldl_contigs_eq_finset_sum {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup)
    (val : ContigEvidence → ℕ) (f : String → ℕ)
    (hmatch : ∀ c ∈ contigs, f c.id = val c) :
    contigs.foldl (fun acc c => acc + val c) 0 = ∑ cid ∈ contigBin contigs, f cid := by
  rw [foldl_add_nat, Nat.zero_add]
  have hmap : contigs.map val = (contigs.map (·.id)).map f := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    exact (hmatch c hc).symm
  rw [hmap]
  exact (List.sum_toFinset f hnodup).symm

/-- **Exact Contig Marker-Count Aggregation Bridge**: When contig IDs are unique,
`Kernel.binMarkerCount` equals `Markers.binCounts`. -/
theorem binMarkerCount_eq_binCounts {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (g : String) :
    binMarkerCount contigs g = binCounts (contigHitsOf contigs) (contigBin contigs) g := by
  unfold binMarkerCount binCounts
  apply foldl_contigs_eq_finset_sum hnodup
  intro c hc
  unfold contigHitsOf
  rw [find?_eq_some_of_mem_nodup hnodup hc]

/-! ### Exact MIMAG & Strain-Heterogeneity Agreement -/

theorem kRNAProfile_satisfiesHQ_eq (r : KRNAProfile) :
    r.satisfiesHQ = (toRNAProfile r).satisfiesHQ := rfl

/-- **Soundness & Completeness of the Executable MIMAG Classifier**:
`toMIMAGTier (kClassifyMIMAG comp cont rna) = Quality.classifyMIMAG comp cont (toRNAProfile rna)`. -/
theorem kClassifyMIMAG_eq_classifyMIMAG (comp cont : ℚ) (rna : KRNAProfile) :
    toMIMAGTier (kClassifyMIMAG comp cont rna) =
      Quality.classifyMIMAG comp cont (toRNAProfile rna) := by
  unfold kClassifyMIMAG Quality.classifyMIMAG
  rw [kRNAProfile_satisfiesHQ_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  split_ifs <;> rfl

theorem kStrainHeterogeneity_eq (h t : ℕ) :
    kStrainHeterogeneity h t = strainHeterogeneity h t := by
  unfold kStrainHeterogeneity strainHeterogeneity
  by_cases ht : t = 0 <;> simp [ht]

theorem kNonStrainCont_eq (cont sh : ℚ) :
    kNonStrainCont cont sh = nonStrainContamination cont sh := rfl

/-! ### Bridge Theorem: Executable `Kernel.kCheckTaxCoherent` → `Taxonomy.TaxCoherent` -/

/-- **Direct Soundness of the Executable Tree-Coherence Checker (`Kernel.kCheckTaxCoherent`)**:
Whenever the CLI's `kCheckTaxCoherent contigs` returns `true` (on a bin with unique contig
IDs, as enforced by `auditMAG`), the bin provably satisfies `Taxonomy.TaxCoherent`,
directly unlocking `Taxonomy.rank_refinement_monotonicity`. -/
theorem kCheckTaxCoherent_sound {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup)
    (h : kCheckTaxCoherent contigs = true) :
    TaxCoherent (contigBin contigs) (contigTaxOf contigs) := by
  unfold kCheckTaxCoherent at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨hpref, htree⟩
  constructor
  · intro cid hcid r₁ r₂ hr hsome
    rcases mem_contigBin_iff.mp hcid with ⟨c, hc, rfl⟩
    have hlook := find?_eq_some_of_mem_nodup hnodup hc
    have hsome' : (contigTax c (fromTaxRank r₂)).isSome = true := by
      simpa [contigTaxOf, hlook] using hsome
    have hle : KTaxRank.le (fromTaxRank r₁) (fromTaxRank r₂) = true := by
      rw [kTaxRank_le_iff, toTaxRank_fromTaxRank, toTaxRank_fromTaxRank]; exact hr
    have hstep := hpref c hc (fromTaxRank r₁) (mem_kTaxRank_all _) (fromTaxRank r₂) (mem_kTaxRank_all _)
    rcases hstep with (hnle | hnsome) | hok
    · rw [hle] at hnle; exact absurd hnle (by decide)
    · rw [hsome'] at hnsome; exact absurd hnsome (by decide)
    · simpa [contigTaxOf, hlook] using hok
  · intro cid₁ hcid₁ cid₂ hcid₂ r₁ r₂ t hr h1 h2
    rcases mem_contigBin_iff.mp hcid₁ with ⟨c₁, hc₁, rfl⟩
    rcases mem_contigBin_iff.mp hcid₂ with ⟨c₂, hc₂, rfl⟩
    have hlook₁ := find?_eq_some_of_mem_nodup hnodup hc₁
    have hlook₂ := find?_eq_some_of_mem_nodup hnodup hc₂
    have h1' : contigTax c₁ (fromTaxRank r₂) = some t := by
      simpa [contigTaxOf, hlook₁] using h1
    have h2' : contigTax c₂ (fromTaxRank r₂) = some t := by
      simpa [contigTaxOf, hlook₂] using h2
    have hle : KTaxRank.le (fromTaxRank r₁) (fromTaxRank r₂) = true := by
      rw [kTaxRank_le_iff, toTaxRank_fromTaxRank, toTaxRank_fromTaxRank]; exact hr
    have hstep := htree c₁ hc₁ c₂ hc₂ (fromTaxRank r₁) (mem_kTaxRank_all _) (fromTaxRank r₂) (mem_kTaxRank_all _)
    rcases hstep with hnle | hmatch
    · rw [hle] at hnle; exact absurd hnle (by decide)
    · rw [h1', h2'] at hmatch
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_self_eq_true, beq_iff_eq,
        Bool.true_eq_false, false_or] at hmatch
      simpa [contigTaxOf, hlook₁, hlook₂] using hmatch

/-! ### Bridge Theorems: Executable `Kernel.kRankAudit` = `MAGLean.Taxonomy` -/

private lemma kTotBp_eq_totalLen {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) :
    ((contigs.foldl (fun acc c => acc + c.length) 0 : ℕ) : ℚ) =
      totalLen (contigBin contigs) (contigLenOf contigs) := by
  have hnat := foldl_contigs_eq_finset_sum hnodup (fun c => c.length) (contigLenOf contigs)
    (fun c hc => by simp [contigLenOf, find?_eq_some_of_mem_nodup hnodup hc])
  rw [hnat, totalLen, Nat.cast_sum]

private lemma foldl_ite_add {β : Type*} (l : List β) (p : β → Bool) (w : β → ℕ) (init : ℕ) :
    l.foldl (fun acc x => if p x then acc + w x else acc) init =
      l.foldl (fun acc x => acc + if p x then w x else 0) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons]
    cases h : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih init
    · simp only [↓reduceIte]
      exact ih (init + w x)

private lemma kClassBp_eq_classifiedLen {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank) :
    ((contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) 0 : ℕ) : ℚ) =
      classifiedLen (contigBin contigs) (contigLenOf contigs) (contigTaxOf contigs) (toTaxRank r) := by
  rw [foldl_ite_add contigs (fun c => (contigTax c r).isSome) (fun c => c.length) 0]
  have hnat := foldl_contigs_eq_finset_sum hnodup
    (fun c => if (contigTax c r).isSome then c.length else 0)
    (fun cid => if (contigTaxOf contigs cid (toTaxRank r)).isSome then contigLenOf contigs cid else 0)
    (fun c hc => by
      simp [contigTaxOf, contigLenOf, find?_eq_some_of_mem_nodup hnodup hc])
  rw [hnat, classifiedLen, totalLen, classifiedAt, Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro cid _
  split_ifs <;> simp

private lemma kTaxonWeight_eq {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank) (t : String) :
    ((contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0 : ℕ) : ℚ) =
      taxonWeight (contigBin contigs) (contigLenOf contigs) (contigTaxOf contigs) (toTaxRank r) t := by
  rw [foldl_ite_add contigs (fun c => contigTax c r == some t) (fun c => c.length) 0]
  have hnat := foldl_contigs_eq_finset_sum hnodup
    (fun c => if contigTax c r == some t then c.length else 0)
    (fun cid => if contigTaxOf contigs cid (toTaxRank r) = some t then contigLenOf contigs cid else 0)
    (fun c hc => by
      simp [contigTaxOf, contigLenOf, find?_eq_some_of_mem_nodup hnodup hc])
  rw [hnat, taxonWeight, Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro cid _
  split_ifs <;> simp

private lemma bestWeight_foldl_max (ts : List String) (w : String → ℕ)
    (init : Option (String × ℕ)) :
    (match ts.foldl (fun acc t =>
        let wt := w t
        match acc with
        | none => some (t, wt)
        | some (bt, bw) => if bw < wt then some (t, wt) else some (bt, bw)) init with
      | none => 0
      | some (_, bw) => bw) =
      ts.foldl (fun acc t => max acc (w t))
        (match init with | none => 0 | some (_, bw) => bw) := by
  induction ts generalizing init with
  | nil => cases init <;> rfl
  | cons t rest ih =>
    simp only [List.foldl_cons]
    cases init with
    | none =>
      rw [ih (some (t, w t))]
      simp
    | some p =>
      rcases p with ⟨bt, bw⟩
      dsimp only
      split_ifs with hlt
      · rw [ih (some (t, w t))]
        simp [max_eq_right (le_of_lt hlt)]
      · rw [ih (some (bt, bw))]
        simp [max_eq_left (not_lt.mp hlt)]

private lemma foldl_max_le_iff (ts : List String) (w : String → ℕ) (init M : ℕ) :
    ts.foldl (fun acc t => max acc (w t)) init ≤ M ↔ init ≤ M ∧ ∀ t ∈ ts, w t ≤ M := by
  induction ts generalizing init with
  | nil => simp
  | cons t rest ih =>
    simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons]
    constructor
    · rintro ⟨⟨hi, ht⟩, hrest⟩
      refine ⟨hi, ?_⟩
      rintro x (rfl | hx)
      · exact ht
      · exact hrest x hx
    · rintro ⟨hi, hall⟩
      exact ⟨⟨hi, hall t (Or.inl rfl)⟩, fun x hx => hall x (Or.inr hx)⟩

private lemma kTaxa_toFinset_eq {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank) :
    (dedupStrings (contigs.filterMap (fun c => contigTax c r))).toFinset =
      taxaAt (contigBin contigs) (contigTaxOf contigs) (toTaxRank r) := by
  ext t
  simp only [dedupStrings_toFinset, List.mem_toFinset, List.mem_filterMap,
    taxaAt, Finset.mem_biUnion, mem_contigBin_iff, Option.mem_toFinset]
  constructor
  · rintro ⟨c, hc, hct⟩
    refine ⟨c.id, ⟨c, hc, rfl⟩, ?_⟩
    simpa [contigTaxOf, find?_eq_some_of_mem_nodup hnodup hc] using hct
  · rintro ⟨cid, ⟨c, hc, rfl⟩, hct⟩
    refine ⟨c, hc, ?_⟩
    simpa [contigTaxOf, find?_eq_some_of_mem_nodup hnodup hc] using hct

private lemma kMaxW_eq_maxTaxonWeight {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank) :
    let taxa := dedupStrings (contigs.filterMap (fun c => contigTax c r))
    let best := taxa.foldl (fun acc t =>
      let w : Nat := contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0
      match acc with
      | none => some (t, w)
      | some (bt, bw) => if bw < w then some (t, w) else some (bt, bw)) none
    let maxW : Nat := match best with | none => 0 | some (_, w) => w
    (maxW : ℚ) = maxTaxonWeight (contigBin contigs) (contigLenOf contigs) (contigTaxOf contigs) (toTaxRank r) := by
  intro taxa best maxW
  let w : String → ℕ := fun t =>
    contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0
  have hmaxW_eq : maxW = taxa.foldl (fun acc t => max acc (w t)) 0 :=
    bestWeight_foldl_max taxa w none
  apply le_antisymm
  · -- `(maxW : ℚ) ≤ maxTaxonWeight`
    by_cases hemp : taxa = []
    · rw [hmaxW_eq, hemp]; simp [maxTaxonWeight_nonneg]
    · have hle_all : ∀ t ∈ taxa, (w t : ℚ) ≤
          maxTaxonWeight (contigBin contigs) (contigLenOf contigs) (contigTaxOf contigs) (toTaxRank r) := by
        intro t _
        rw [kTaxonWeight_eq hnodup r t]
        exact taxonWeight_le_maxTaxonWeight _ _ _ _ t
      -- Show `maxW` is attained by `0` or some `t ∈ taxa`
      have hatt : maxW = 0 ∨ ∃ t ∈ taxa, maxW = w t := by
        rw [hmaxW_eq]
        suffices ∀ (ts : List String) (init : ℕ),
            ts.foldl (fun acc t => max acc (w t)) init = init ∨
              ∃ t ∈ ts, ts.foldl (fun acc t => max acc (w t)) init = w t by
          exact this taxa 0
        intro ts
        induction ts with
        | nil => intro init; left; rfl
        | cons t rest ih =>
          intro init
          simp only [List.foldl_cons]
          rcases ih (max init (w t)) with hinit | ⟨t', ht', heq⟩
          · rcases le_total init (w t) with hle | hle
            · right; refine ⟨t, List.mem_cons_self, ?_⟩
              rw [hinit, max_eq_right hle]
            · left; rw [hinit, max_eq_left hle]
          · right; exact ⟨t', List.mem_cons_of_mem _ ht', heq⟩
      rcases hatt with h0 | ⟨t, ht, heq⟩
      · rw [h0, Nat.cast_zero]; exact maxTaxonWeight_nonneg _ _ _ _
      · rw [heq]; exact hle_all t ht
  · -- `maxTaxonWeight ≤ (maxW : ℚ)`
    rw [maxTaxonWeight_le_iff _ _ _ _ (by positivity)]
    intro t
    by_cases ht : t ∈ taxaAt (contigBin contigs) (contigTaxOf contigs) (toTaxRank r)
    · have ht_mem : t ∈ taxa := by
        have := kTaxa_toFinset_eq hnodup r
        rw [← this, List.mem_toFinset] at ht
        exact ht
      rw [← kTaxonWeight_eq hnodup r t]
      have hle_nat : w t ≤ maxW := by
        have h := (foldl_max_le_iff taxa w 0 maxW).mp (by rw [← hmaxW_eq])
        exact h.2 t ht_mem
      exact_mod_cast hle_nat
    · have hzero : taxonWeight (contigBin contigs) (contigLenOf contigs) (contigTaxOf contigs) (toTaxRank r) t = 0 := by
        unfold taxonWeight
        apply Finset.sum_eq_zero
        intro cid hcid
        exfalso
        simp only [Finset.mem_filter] at hcid
        apply ht
        unfold taxaAt
        exact Finset.mem_biUnion.mpr ⟨cid, hcid.1, by simp [hcid.2]⟩
      rw [hzero]; positivity

private lemma kClassBp_le_kTotBp (contigs : List ContigEvidence) (r : KTaxRank) :
    contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) 0 ≤
      contigs.foldl (fun acc c => acc + c.length) 0 := by
  suffices ∀ a b, a ≤ b →
      contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) a ≤
        contigs.foldl (fun acc c => acc + c.length) b by
    exact this 0 0 (le_refl 0)
  induction contigs with
  | nil => intro a b hab; exact hab
  | cons c rest ih =>
    intro a b hab
    simp only [List.foldl_cons]
    split_ifs
    · exact ih _ _ (by omega)
    · exact ih _ _ (by omega)

private lemma kUnclassBp_eq_unclassifiedLen {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank) :
    let totBp := contigs.foldl (fun acc c => acc + c.length) 0
    let classBp := contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) 0
    ((totBp - classBp : ℕ) : ℚ) =
      unclassifiedLen (contigBin contigs) (contigLenOf contigs) (contigTaxOf contigs) (toTaxRank r) := by
  intro totBp classBp
  have hle : classBp ≤ totBp := kClassBp_le_kTotBp contigs r
  have hsub : ((totBp - classBp : ℕ) : ℚ) = (totBp : ℚ) - (classBp : ℚ) :=
    Nat.cast_sub hle
  rw [hsub, kTotBp_eq_totalLen hnodup, kClassBp_eq_classifiedLen hnodup r]
  have hsum := classifiedLen_add_unclassifiedLen (contigBin contigs) (contigLenOf contigs)
    (contigTaxOf contigs) (toTaxRank r)
  linarith

/-- **Exact Bridge for `Kernel.kRankAudit` (Purity, Optimistic Purity, Drop Purity,
Chimerism, and Unclassified Fraction)**:
For every bin with unique contig IDs and every rank `r`, all five rational fields of
`Kernel.kRankAudit contigs r` equal the formal `MAGLean.Taxonomy` definitions identically. -/
theorem kRankAudit_eq_taxonomy {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank) :
    let B := contigBin contigs
    let len := contigLenOf contigs
    let τ := contigTaxOf contigs
    let rk := toTaxRank r
    let ra := kRankAudit contigs r
    ra.purityCons = purityCons B len τ rk ∧
    ra.purityOpt = purityOpt B len τ rk ∧
    ra.purityDrop = purityDrop B len τ rk ∧
    ra.chimerism = chimerismScore B len τ rk ∧
    ra.unclassifiedFrac =
      if totalLen B len = 0 then 0 else unclassifiedLen B len τ rk / totalLen B len := by
  intro B len τ rk ra
  have htot := kTotBp_eq_totalLen hnodup
  have hcls := kClassBp_eq_classifiedLen hnodup r
  have hunc := kUnclassBp_eq_unclassifiedLen hnodup r
  have hmax := kMaxW_eq_maxTaxonWeight hnodup r
  have hmax_snd :
      ((match (dedupStrings (contigs.filterMap (fun c => contigTax c r))).foldl (fun acc t =>
          match acc with
          | none => some (t, contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0)
          | some (bt, bw) =>
            if bw < contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0 then
              some (t, contigs.foldl (fun s c => if contigTax c r == some t then s + c.length else s) 0)
            else some (bt, bw)) none with
        | none => (none, 0)
        | some (t, w) => (some t, w)).2 : ℚ) =
      maxTaxonWeight B len τ rk := by
    rw [← hmax]
    dsimp only
    congr 1
    have hpair : ∀ x : Option (String × ℕ),
        (match x with | none => ((none : Option String), 0) | some (t, w) => (some t, w)).2 =
          match x with | none => 0 | some (_, w) => w := fun x => by cases x <;> rfl
    exact hpair _
  have htot_zero :
      (contigs.foldl (fun acc c => acc + c.length) 0 == 0) = true ↔ totalLen B len = 0 := by
    rw [beq_iff_eq, ← htot]
    exact Nat.cast_eq_zero.symm
  have hcls_zero :
      (contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) 0 == 0) = true ↔
        classifiedLen B len τ rk = 0 := by
    rw [beq_iff_eq, ← hcls]
    exact Nat.cast_eq_zero.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- purityCons
    dsimp only [ra, kRankAudit]
    unfold purityCons
    by_cases h0 : totalLen B len = 0
    · have hb := htot_zero.mpr h0; simp [hb, h0]
    · have hb : (contigs.foldl (fun acc c => acc + c.length) 0 == 0) = false :=
        Bool.eq_false_iff.mpr (fun ht => h0 (htot_zero.mp ht))
      simp only [hb, Bool.false_eq_true, ↓reduceIte, h0]
      exact congrArg₂ (· / ·) hmax_snd htot
  · -- purityOpt
    dsimp only [ra, kRankAudit]
    unfold purityOpt
    by_cases h0 : totalLen B len = 0
    · have hb := htot_zero.mpr h0; simp [hb, h0]
    · have hb : (contigs.foldl (fun acc c => acc + c.length) 0 == 0) = false :=
        Bool.eq_false_iff.mpr (fun ht => h0 (htot_zero.mp ht))
      simp only [hb, Bool.false_eq_true, ↓reduceIte, h0]
      exact congrArg₂ (· / ·) (congrArg₂ (· + ·) hmax_snd hunc) htot
  · -- purityDrop
    dsimp only [ra, kRankAudit]
    unfold purityDrop
    by_cases h0 : classifiedLen B len τ rk = 0
    · have hb := hcls_zero.mpr h0; simp [hb, h0]
    · have hb : (contigs.foldl (fun acc c => if (contigTax c r).isSome then acc + c.length else acc) 0 == 0) = false :=
        Bool.eq_false_iff.mpr (fun ht => h0 (hcls_zero.mp ht))
      simp only [hb, Bool.false_eq_true, ↓reduceIte, h0]
      exact congrArg₂ (· / ·) hmax_snd hcls
  · -- chimerism
    dsimp only [ra, kRankAudit]
    unfold chimerismScore purityCons
    by_cases h0 : totalLen B len = 0
    · have hb := htot_zero.mpr h0; simp [hb, h0]
    · have hb : (contigs.foldl (fun acc c => acc + c.length) 0 == 0) = false :=
        Bool.eq_false_iff.mpr (fun ht => h0 (htot_zero.mp ht))
      simp only [hb, Bool.false_eq_true, ↓reduceIte, h0]
      exact congrArg (1 - ·) (congrArg₂ (· / ·) hmax_snd htot)
  · -- unclassifiedFrac
    dsimp only [ra, kRankAudit]
    by_cases h0 : totalLen B len = 0
    · have hb := htot_zero.mpr h0; simp [hb, h0]
    · have hb : (contigs.foldl (fun acc c => acc + c.length) 0 == 0) = false :=
        Bool.eq_false_iff.mpr (fun ht => h0 (htot_zero.mp ht))
      simp only [hb, Bool.false_eq_true, ↓reduceIte, h0]
      exact congrArg₂ (· / ·) hunc htot

/-- **Soundness of the CLI's `STEALTH_CHIMERA_ALERT` Threshold**:
Whenever `(kRankAudit contigs r).purityOpt < 9 / 10` on a positive-length bin with unique
contig IDs, *every* possible taxonomic completion `τ'` of the unclassified contigs that
agrees with the classified contigs provably has full-bin purity `< 9 / 10`. -/
theorem kRankAudit_stealth_alert_sound {contigs : List ContigEvidence}
    (hnodup : (contigs.map (·.id)).Nodup) (r : KTaxRank)
    (htot : 0 < totalLen (contigBin contigs) (contigLenOf contigs))
    (halert : (kRankAudit contigs r).purityOpt < (9 / 10 : ℚ))
    (τ' : String → TaxRank → Option String)
    (hagree : ∀ cid ∈ contigBin contigs, ∀ t,
      contigTaxOf contigs cid (toTaxRank r) = some t → τ' cid (toTaxRank r) = some t) :
    purityCons (contigBin contigs) (contigLenOf contigs) τ' (toTaxRank r) < (9 / 10 : ℚ) := by
  have heq := (kRankAudit_eq_taxonomy hnodup r).2.1
  have hsand := purity_unclassified_sandwich (contigBin contigs) (contigLenOf contigs)
    (contigTaxOf contigs) τ' (toTaxRank r) htot hagree
  linarith [hsand.2.1]

/-! ### Verified Bridge from Rational CLI Radius to Real-Analysis Hoeffding Bounds -/

/-- **Rational-to-Real Hoeffding 95% Certificate Theorem**:
If a rational radius `ε > 0` satisfies `2 ≤ (k : ℚ) * ε ^ 2`, then under the
independent Bernoulli observation model (`MAGLean.Probabilistic`),
`Pr(|empComp - p| ≥ ε) ≤ 1 / 20` (certified ≥ 95% confidence interval). -/
theorem hoeffding95_cert_sound {k : ℕ} (hk : 0 < k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ε : ℚ} (hε : 0 < ε)
    (hcert : (2 : ℚ) ≤ (k : ℚ) * (ε * ε)) :
    ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin k → Bool => (ε : ℝ) ≤ |Probabilistic.empComp ω - p|),
      Probabilistic.bernProb p ω ≤ (1 / 20 : ℝ) := by
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hcert_r : (2 : ℝ) ≤ (k : ℝ) * ((ε : ℝ) * (ε : ℝ)) := by exact_mod_cast hcert
  have hexp1 : (27 / 10 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have hexp4 : (40 : ℝ) ≤ Real.exp 4 := by
    have hpow : ((27 / 10 : ℝ) ^ 4) < (Real.exp 1) ^ 4 :=
      pow_lt_pow_left₀ hexp1 (by norm_num) (by norm_num)
    have he4 : (Real.exp 1) ^ 4 = Real.exp 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he4] at hpow
    norm_num at hpow
    linarith
  have hlog40 : Real.log (2 / (1 / 20 : ℝ)) ≤ 4 := by
    have h40 : (2 / (1 / 20 : ℝ)) = 40 := by norm_num
    rw [h40, Real.log_le_iff_le_exp (by norm_num)]
    exact hexp4
  have hsize : Real.log (2 / (1 / 20 : ℝ)) / (2 * (ε : ℝ) ^ 2) ≤ (k : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq (ε : ℝ)]
  exact Probabilistic.marker_count_sufficient hk hp0 hp1 hεr (by norm_num) hsize

theorem certifiedHoeffding95Radius_pos (k : ℕ) :
    0 < Kernel.certifiedHoeffding95Radius k := by
  unfold Kernel.certifiedHoeffding95Radius
  split_ifs
  · norm_num
  · suffices ∀ m fuel, 0 < m → 0 < Kernel.certifiedHoeffding95Radius.go k m fuel by
      exact this 1 1000 (by omega)
    intro m fuel
    induction fuel generalizing m with
    | zero => intro _; simp [Kernel.certifiedHoeffding95Radius.go]
    | succ f ih =>
      intro hm
      unfold Kernel.certifiedHoeffding95Radius.go
      dsimp only
      split_ifs
      · positivity
      · exact ih (m + 1) (by omega)

theorem certifiedHoeffding95Radius_valid {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℚ) ≤ (k : ℚ) * (Kernel.certifiedHoeffding95Radius k * Kernel.certifiedHoeffding95Radius k) := by
  unfold Kernel.certifiedHoeffding95Radius
  have hnotlt : ¬ k < 2 := by omega
  simp only [hnotlt, ↓reduceIte]
  suffices ∀ m fuel, (2 : ℚ) ≤ (k : ℚ) * (1 * 1) →
      (2 : ℚ) ≤ (k : ℚ) *
        (Kernel.certifiedHoeffding95Radius.go k m fuel *
          Kernel.certifiedHoeffding95Radius.go k m fuel) by
    apply this 1 1000
    have hkq : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    linarith
  intro m fuel hbase
  induction fuel generalizing m with
  | zero => simpa [Kernel.certifiedHoeffding95Radius.go] using hbase
  | succ f ih =>
    unfold Kernel.certifiedHoeffding95Radius.go
    dsimp only
    split_ifs with h
    · exact h
    · exact ih (m + 1)

/-- **End-to-End Soundness of the CLI's 95% Hoeffding Radius** (under the independent
Bernoulli observation model): for every `k ≥ 2`, `ε = Kernel.certifiedHoeffding95Radius k`
provably satisfies `Pr(|empComp - p| ≥ ε) ≤ 0.05`. -/
theorem kernel_hoeffding95_sound {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let ε := Kernel.certifiedHoeffding95Radius k
    ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin k → Bool => (ε : ℝ) ≤ |Probabilistic.empComp ω - p|),
      Probabilistic.bernProb p ω ≤ (1 / 20 : ℝ) :=
  hoeffding95_cert_sound (by omega) hp0 hp1
    (certifiedHoeffding95Radius_pos k) (certifiedHoeffding95Radius_valid hk)

end MAGLean.Certificate
