import MAGLean.Markers

/-!
# MAGLean.Taxonomy

Formal theory of taxonomic hierarchies, lineage-specific marker loss (DPANN /
Patescibacteria / symbionts), safe LCA rank selection, and contig-level taxonomic
purity / GUNC-style chimerism guarantees across taxonomic ranks.

## Main Results

* `lineage_loss_bias_bound`: If clade `v` lacks fraction `λ = lossRate M (core v)` of
  ancestral marker family `M`, then *any* pure genome from `v` has apparent completeness
  at most `1 - λ` (and exact `1 - λ` for a 100% biologically complete genome).
* `lca_zero_lineage_loss`: Under ancestral core conservation, evaluating a MAG with
  phylogenetic placement uncertainty set `U` at `lca(U)` guarantees zero lineage-loss bias
  across all candidate clades in `U`.
* `purity_unclassified_sandwich`: Exact worst-case (`purityCons`) and best-case
  (`purityOpt`) purity bounds for *any* true assignment of unclassified contigs, with
  gap equal to the unclassified base-pair fraction.
* `rank_refinement_monotonicity`: Under tree-coherent contig taxonomy, conservative
  purity is monotonically non-increasing (and chimerism non-decreasing) as you descend
  from Domain to Species.
* `unclassified_dilution_counterexample`: Explicit chimeric bin where dropping
  unclassified contigs causes apparent purity to *jump* from `1/2` (phylum) to `1` (genus).
* `taxonomic_catches_stealth_chimera`: Merging two disjoint clades `t₁ ≠ t₂` forces
  `purityCons = max(W₁, W₂) / (W₁ + W₂) < 1`, closing the marker-only stealth-chimera
  loophole from `MAGLean.Markers`.
-/

namespace MAGLean.Taxonomy

/-! ### Clade Hierarchy & LCA -/

/-- A rooted taxonomic hierarchy formalized as a meet-semilattice of clades, where
`le u v` means `u` is an ancestor of `v` (coarser or equal rank) and `lca u v` is
their lowest common ancestor. -/
structure CladeHierarchy (Taxon : Type*) [DecidableEq Taxon] where
  le : Taxon → Taxon → Prop
  le_refl : ∀ u, le u u
  le_trans : ∀ u v w, le u v → le v w → le u w
  le_antisymm : ∀ u v, le u v → le v u → u = v
  lca : Taxon → Taxon → Taxon
  lca_le_left : ∀ u v, le (lca u v) u
  lca_le_right : ∀ u v, le (lca u v) v
  le_lca : ∀ w u v, le w u → le w v → le w (lca u v)

namespace CladeHierarchy

variable {Taxon : Type*} [DecidableEq Taxon]

/-- Computable lowest common ancestor of a nonempty list of candidate clades `u :: us`. -/
def lcaList (H : CladeHierarchy Taxon) (u : Taxon) (us : List Taxon) : Taxon :=
  us.foldl H.lca u

lemma lcaList_le_init (H : CladeHierarchy Taxon) (u : Taxon) (us : List Taxon) :
    H.le (H.lcaList u us) u := by
  unfold lcaList
  induction us generalizing u with
  | nil => exact H.le_refl u
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact H.le_trans _ _ _ (ih (H.lca u v)) (H.lca_le_left u v)

/-- `lcaList u us` is an ancestor of every clade in `u :: us`. -/
theorem lcaList_le_mem (H : CladeHierarchy Taxon) (u : Taxon) (us : List Taxon)
    {x : Taxon} (hx : x ∈ u :: us) :
    H.le (H.lcaList u us) x := by
  induction us generalizing u with
  | nil =>
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact H.le_refl u
  | cons v vs ih =>
    rcases List.mem_cons.mp hx with hxu | hx'
    · rw [hxu]
      exact H.lcaList_le_init u (v :: vs)
    · rcases List.mem_cons.mp hx' with hxv | hx''
      · rw [hxv]
        unfold lcaList
        simp only [List.foldl_cons]
        exact H.le_trans _ _ _ (H.lcaList_le_init (H.lca u v) vs) (H.lca_le_right u v)
      · unfold lcaList
        simp only [List.foldl_cons]
        exact ih (H.lca u v) (List.mem_cons_of_mem _ hx'')

/-- `lcaList u us` is the *greatest* (most specific) common ancestor of `u :: us`. -/
theorem le_lcaList (H : CladeHierarchy Taxon) (w u : Taxon) (us : List Taxon)
    (h : ∀ x ∈ u :: us, H.le w x) :
    H.le w (H.lcaList u us) := by
  unfold lcaList
  induction us generalizing u with
  | nil => exact h u (by simp)
  | cons v vs ih =>
    simp only [List.foldl_cons]
    apply ih (H.lca u v)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact H.le_lca w u v (h u (by simp)) (h v (by simp))
    · exact h x (by simp [hx'])

end CladeHierarchy

/-! ### Lineage-Specific Marker Loss & Safe LCA Rank Selection -/

section LineageLoss

variable {α : Type*} [DecidableEq α]

/-- Fraction of markers in collocated set `s` that are genuinely absent from clade
core repertoire `core`. -/
def setLoss (s core : Finset α) : ℚ :=
  ((s \ core).card : ℚ) / (s.card : ℚ)

/-- Weighted lineage-loss fraction of marker family `M` on clade core `core`. -/
def lossRate (M : MarkerFamily α) (core : Finset α) : ℚ :=
  (M.sets.map (fun s => setLoss s core)).sum / (M.numSets : ℚ)

/-- The 100%-complete single-copy genome profile of a clade with true repertoire `core`. -/
def fullGenome (core : Finset α) : α → ℕ :=
  fun g => if g ∈ core then 1 else 0

private lemma list_sum_map_le' {β : Type*} (l : List β) (u v : β → ℚ)
    (h : ∀ x ∈ l, u x ≤ v x) : (l.map u).sum ≤ (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private lemma list_sum_map_const' {β : Type*} (l : List β) (c : ℚ) :
    (l.map (fun _ => c)).sum = (l.length : ℚ) * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

private lemma list_sum_map_sub' {β : Type*} (l : List β) (u v : β → ℚ) :
    (l.map (fun x => u x - v x)).sum = (l.map u).sum - (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma setComp_le_one_sub_setLoss {s core : Finset α} (hs : s.Nonempty)
    {f : α → ℕ} (hsub : ∀ g, 0 < f g → g ∈ core) :
    setComp s f ≤ 1 - setLoss s core := by
  unfold setComp setLoss
  have hpos : (0 : ℚ) < (s.card : ℚ) := by exact_mod_cast hs.card_pos
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt hpos
  have hcard_eq : (s ∩ core).card + (s \ core).card = s.card := Finset.card_inter_add_card_sdiff s core
  have hsum_le : ∑ g ∈ s, (present (f g) : ℚ) ≤ ((s ∩ core).card : ℚ) := by
    calc ∑ g ∈ s, (present (f g) : ℚ)
        ≤ ∑ g ∈ s, (if g ∈ core then (1 : ℚ) else 0) := by
          apply Finset.sum_le_sum
          intro g _
          by_cases hgc : g ∈ core
          · simp only [hgc, ↓reduceIte]
            exact_mod_cast present_le_one (f g)
          · simp only [hgc, ↓reduceIte]
            have hfg0 : f g = 0 := by
              by_contra hnz
              exact hgc (hsub g (Nat.pos_of_ne_zero hnz))
            simp [hfg0]
      _ = ((s ∩ core).card : ℚ) := by
          rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  have hcard_q : ((s ∩ core).card : ℚ) = (s.card : ℚ) - ((s \ core).card : ℚ) := by
    have : ((s ∩ core).card : ℚ) + ((s \ core).card : ℚ) = (s.card : ℚ) := by exact_mod_cast hcard_eq
    linarith
  rw [hcard_q] at hsum_le
  calc (∑ g ∈ s, (present (f g) : ℚ)) / (s.card : ℚ)
      ≤ ((s.card : ℚ) - ((s \ core).card : ℚ)) / (s.card : ℚ) :=
        div_le_div_of_nonneg_right hsum_le (le_of_lt hpos)
    _ = 1 - ((s \ core).card : ℚ) / (s.card : ℚ) := by field_simp [hne]

lemma setComp_fullGenome {s core : Finset α} (hs : s.Nonempty) :
    setComp s (fullGenome core) = 1 - setLoss s core := by
  unfold setComp setLoss fullGenome
  have hpos : (0 : ℚ) < (s.card : ℚ) := by exact_mod_cast hs.card_pos
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt hpos
  have hcard_eq : (s ∩ core).card + (s \ core).card = s.card := Finset.card_inter_add_card_sdiff s core
  have hsum : ∑ g ∈ s, (present (if g ∈ core then 1 else 0) : ℚ) = ((s ∩ core).card : ℚ) := by
    have hpt : ∀ g ∈ s, (present (if g ∈ core then 1 else 0) : ℚ) = if g ∈ core then 1 else 0 := by
      intro g _
      by_cases h : g ∈ core <;> simp [h]
    rw [Finset.sum_congr rfl hpt]
    simp only [Finset.sum_boole]
    rw [Finset.filter_mem_eq_inter]
  rw [hsum]
  have hcard_q : ((s ∩ core).card : ℚ) = (s.card : ℚ) - ((s \ core).card : ℚ) := by
    have : ((s ∩ core).card : ℚ) + ((s \ core).card : ℚ) = (s.card : ℚ) := by exact_mod_cast hcard_eq
    linarith
  rw [hcard_q]
  field_simp [hne]

/-- **Lineage-Loss Bias Theorem (DPANN / Patescibacteria / Symbiont Ceiling)**:
If a bin `f` only contains genes from a reduced-genome clade `core`, evaluating it with
an ancestral marker family `M` guarantees apparent completeness `≤ 1 - lossRate M core`. -/
theorem lineage_loss_bias_bound (M : MarkerFamily α) (core : Finset α)
    {f : α → ℕ} (hsub : ∀ g, 0 < f g → g ∈ core) :
    completeness M f ≤ 1 - lossRate M core := by
  unfold completeness lossRate
  have hpos := M.numSets_pos_rat
  have hne := ne_of_gt hpos
  have hle : (M.sets.map (fun s => setComp s f)).sum ≤
      (M.sets.map (fun s => 1 - setLoss s core)).sum :=
    list_sum_map_le' M.sets _ _ (fun s hs => setComp_le_one_sub_setLoss (M.mem_nonempty s hs) hsub)
  rw [list_sum_map_sub', list_sum_map_const', mul_one] at hle
  calc (M.sets.map (fun s => setComp s f)).sum / (M.numSets : ℚ)
      ≤ ((M.numSets : ℚ) - (M.sets.map (fun s => setLoss s core)).sum) / (M.numSets : ℚ) :=
        div_le_div_of_nonneg_right hle (le_of_lt hpos)
    _ = 1 - (M.sets.map (fun s => setLoss s core)).sum / (M.numSets : ℚ) := by
        field_simp [hne]

/-- For a 100% biologically complete genome of clade `core`, ancestral completeness equals
`1 - lossRate M core` identically, with zero contamination. -/
theorem lineage_loss_exact_complete (M : MarkerFamily α) (core : Finset α) :
    completeness M (fullGenome core) = 1 - lossRate M core ∧
    contamination M (fullGenome core) = 0 := by
  constructor
  · unfold completeness lossRate
    have hne := ne_of_gt M.numSets_pos_rat
    have hmap : M.sets.map (fun s => setComp s (fullGenome core)) =
        M.sets.map (fun s => 1 - setLoss s core) :=
      List.map_congr_left (fun s hs => setComp_fullGenome (M.mem_nonempty s hs))
    rw [hmap, list_sum_map_sub', list_sum_map_const', mul_one]
    change ((M.numSets : ℚ) - (M.sets.map (fun s => setLoss s core)).sum) / (M.numSets : ℚ) =
      1 - (M.sets.map (fun s => setLoss s core)).sum / (M.numSets : ℚ)
    field_simp [hne]
  · unfold contamination setCont fullGenome
    have hzero : ∀ s ∈ M.sets,
        (∑ g ∈ s, (excess (if g ∈ core then 1 else 0) : ℚ)) / (s.card : ℚ) = 0 := by
      intro s _
      have hpt : ∀ g ∈ s, (excess (if g ∈ core then 1 else 0) : ℚ) = 0 := by
        intro g _
        by_cases h : g ∈ core <;> simp [h, excess]
      simp [Finset.sum_eq_zero hpt]
    rw [List.map_congr_left hzero, list_sum_map_const']
    simp

/-- If every marker in `M` belongs to `core`, then `lossRate M core = 0`. -/
theorem lossRate_eq_zero_of_subset (M : MarkerFamily α) (core : Finset α)
    (hcons : ∀ g ∈ M.allMarkers, g ∈ core) :
    lossRate M core = 0 := by
  unfold lossRate setLoss
  have hzero : ∀ s ∈ M.sets, ((s \ core).card : ℚ) / (s.card : ℚ) = 0 := by
    intro s hs
    have hempty : s \ core = ∅ := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      intro g hg
      exact hcons g (MarkerFamily.mem_allMarkers.mpr ⟨s, hs, hg⟩)
    simp [hempty]
  rw [List.map_congr_left hzero, list_sum_map_const']
  simp

/-- **Safe Rank Selection (LCA) Theorem**:
Under ancestral core conservation (`H.le u v → markerSet u ⊆ core v`), evaluating a MAG
whose phylogenetic placement uncertainty set is `u :: us` at `u* = H.lcaList u us`
guarantees **zero lineage-loss bias** for every candidate clade `v ∈ u :: us`. -/
theorem lca_zero_lineage_loss {Taxon : Type*} [DecidableEq Taxon]
    (H : CladeHierarchy Taxon)
    (markerSet : Taxon → MarkerFamily α)
    (core : Taxon → Finset α)
    (hcons : ∀ u v, H.le u v → ∀ g ∈ (markerSet u).allMarkers, g ∈ core v)
    (u : Taxon) (us : List Taxon) :
    let uStar := H.lcaList u us
    ∀ v ∈ u :: us,
      lossRate (markerSet uStar) (core v) = 0 ∧
      completeness (markerSet uStar) (fullGenome (core v)) = 1 := by
  intro uStar v hv
  have hle : H.le uStar v := H.lcaList_le_mem u us hv
  have hloss : lossRate (markerSet uStar) (core v) = 0 :=
    lossRate_eq_zero_of_subset (markerSet uStar) (core v) (hcons uStar v hle)
  refine ⟨hloss, ?_⟩
  rw [(lineage_loss_exact_complete (markerSet uStar) (core v)).1, hloss, sub_zero]

end LineageLoss

/-! ### Contig-Level Taxonomic Coherence, Purity & Chimerism -/

section ContigPurity

variable {Contig Taxon : Type*} [DecidableEq Contig] [DecidableEq Taxon]

/-- Total base-pair length of a bin `B`. -/
def totalLen (B : Finset Contig) (len : Contig → ℕ) : ℚ :=
  ∑ c ∈ B, (len c : ℚ)

/-- Contigs in `B` classified at rank `r`. -/
def classifiedAt (B : Finset Contig) (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    Finset Contig :=
  B.filter (fun c => (τ c r).isSome)

/-- Contigs in `B` unclassified at rank `r`. -/
def unclassifiedAt (B : Finset Contig) (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    Finset Contig :=
  B.filter (fun c => (τ c r).isNone)

/-- Total classified base-pair length at rank `r`. -/
def classifiedLen (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  totalLen (classifiedAt B τ r) len

/-- Total unclassified base-pair length at rank `r`. -/
def unclassifiedLen (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  totalLen (unclassifiedAt B τ r) len

/-- Set of distinct taxa assigned to at least one contig in `B` at rank `r`. -/
def taxaAt (B : Finset Contig) (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    Finset Taxon :=
  B.biUnion (fun c => (τ c r).toFinset)

/-- Total base-pair weight assigned to taxon `t` at rank `r`. -/
def taxonWeight (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) (t : Taxon) : ℚ :=
  ∑ c ∈ B.filter (fun c => τ c r = some t), (len c : ℚ)

/-- Dominant clade base-pair weight in `B` at rank `r` (`0` if no contigs classified). -/
def maxTaxonWeight (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  if h : (taxaAt B τ r).Nonempty then
    (taxaAt B τ r).sup' h (taxonWeight B len τ r)
  else
    0

/-- **Conservative taxonomic purity**: dominant clade bp divided by *total* bin bp
(unclassified contigs count against purity). -/
def purityCons (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  if totalLen B len = 0 then 0 else maxTaxonWeight B len τ r / totalLen B len

/-- **Optimistic taxonomic purity**: assumes all unclassified bp belong to the
dominant clade. -/
def purityOpt (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  if totalLen B len = 0 then 0
  else (maxTaxonWeight B len τ r + unclassifiedLen B len τ r) / totalLen B len

/-- **Drop-unclassified purity**: dominant clade bp divided by *classified* bp only
(subject to unclassified-contig dilution!). -/
def purityDrop (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  if classifiedLen B len τ r = 0 then 0
  else maxTaxonWeight B len τ r / classifiedLen B len τ r

/-- Conservative chimerism / impurity score at rank `r`: `1 - purityCons`. -/
def chimerismScore (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) : ℚ :=
  1 - purityCons B len τ r

/-- Tree-coherence predicate for contig taxonomic lineages in bin `B`:
1. Prefix-closed: classified at rank `r₂` implies classified at every coarser rank `r₁ ≤ r₂`.
2. Tree-consistent: agreeing at rank `r₂` implies agreeing at every coarser rank `r₁ ≤ r₂`. -/
structure TaxCoherent (B : Finset Contig) (τ : Contig → TaxRank → Option Taxon) : Prop where
  prefix_closed : ∀ c ∈ B, ∀ r₁ r₂, r₁ ≤ r₂ → (τ c r₂).isSome → (τ c r₁).isSome
  tree_consistent : ∀ c₁ ∈ B, ∀ c₂ ∈ B, ∀ r₁ r₂ t,
    r₁ ≤ r₂ → τ c₁ r₂ = some t → τ c₂ r₂ = some t → τ c₁ r₁ = τ c₂ r₁

/-! ### Fundamental Weight & Purity Lemmas -/

omit [DecidableEq Contig] in
lemma totalLen_nonneg (B : Finset Contig) (len : Contig → ℕ) :
    0 ≤ totalLen B len := by
  unfold totalLen
  exact Finset.sum_nonneg (fun _ _ => by positivity)

omit [DecidableEq Taxon] in
lemma classifiedLen_add_unclassifiedLen (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    classifiedLen B len τ r + unclassifiedLen B len τ r = totalLen B len := by
  unfold classifiedLen unclassifiedLen totalLen classifiedAt unclassifiedAt
  rw [← Finset.sum_union]
  · congr 1
    ext c
    simp only [Finset.mem_union, Finset.mem_filter]
    cases τ c r <;> simp
  · rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [Finset.mem_filter] at hc1 hc2
    cases h : τ c r <;> simp [h] at hc1 hc2

omit [DecidableEq Contig] in
lemma taxonWeight_nonneg (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) (t : Taxon) :
    0 ≤ taxonWeight B len τ r t := by
  unfold taxonWeight
  exact Finset.sum_nonneg (fun _ _ => by positivity)

omit [DecidableEq Contig] in
lemma taxonWeight_le_classifiedLen (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) (t : Taxon) :
    taxonWeight B len τ r t ≤ classifiedLen B len τ r := by
  unfold taxonWeight classifiedLen totalLen classifiedAt
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, by simp [hc.2]⟩
  · intro _ _ _; positivity

omit [DecidableEq Contig] in
lemma maxTaxonWeight_nonneg (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    0 ≤ maxTaxonWeight B len τ r := by
  unfold maxTaxonWeight
  split_ifs with h
  · rcases h with ⟨t, ht⟩
    exact le_trans (taxonWeight_nonneg B len τ r t) (Finset.le_sup' (taxonWeight B len τ r) ht)
  · exact le_refl 0

lemma taxonWeight_le_maxTaxonWeight (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) (t : Taxon) :
    taxonWeight B len τ r t ≤ maxTaxonWeight B len τ r := by
  by_cases ht : t ∈ taxaAt B τ r
  · unfold maxTaxonWeight
    split_ifs with hne
    · exact Finset.le_sup' (taxonWeight B len τ r) ht
    · exact absurd ⟨t, ht⟩ hne
  · have hzero : taxonWeight B len τ r t = 0 := by
      unfold taxonWeight
      apply Finset.sum_eq_zero
      intro c hc
      exfalso
      simp only [Finset.mem_filter] at hc
      apply ht
      unfold taxaAt
      exact Finset.mem_biUnion.mpr ⟨c, hc.1, by simp [hc.2]⟩
    rw [hzero]
    exact maxTaxonWeight_nonneg B len τ r

lemma maxTaxonWeight_le_iff (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) {M : ℚ} (hM : 0 ≤ M) :
    maxTaxonWeight B len τ r ≤ M ↔ ∀ t, taxonWeight B len τ r t ≤ M := by
  constructor
  · intro h t
    exact le_trans (taxonWeight_le_maxTaxonWeight B len τ r t) h
  · intro h
    unfold maxTaxonWeight
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun t _ => h t)
    · exact hM

lemma maxTaxonWeight_le_classifiedLen (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    maxTaxonWeight B len τ r ≤ classifiedLen B len τ r := by
  have hnn : 0 ≤ classifiedLen B len τ r := totalLen_nonneg (classifiedAt B τ r) len
  rw [maxTaxonWeight_le_iff B len τ r hnn]
  intro t
  exact taxonWeight_le_classifiedLen B len τ r t

theorem purityCons_le_one (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    purityCons B len τ r ≤ 1 := by
  unfold purityCons
  split_ifs with h0
  · norm_num
  · have hpos : 0 < totalLen B len := lt_of_le_of_ne (totalLen_nonneg B len) (Ne.symm h0)
    rw [div_le_one hpos]
    have h1 := maxTaxonWeight_le_classifiedLen B len τ r
    have h2 := classifiedLen_add_unclassifiedLen B len τ r
    have h3 : 0 ≤ unclassifiedLen B len τ r := totalLen_nonneg _ _
    linarith

theorem purityOpt_le_one (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (r : TaxRank) :
    purityOpt B len τ r ≤ 1 := by
  unfold purityOpt
  split_ifs with h0
  · norm_num
  · have hpos : 0 < totalLen B len := lt_of_le_of_ne (totalLen_nonneg B len) (Ne.symm h0)
    rw [div_le_one hpos]
    have h1 := maxTaxonWeight_le_classifiedLen B len τ r
    have h2 := classifiedLen_add_unclassifiedLen B len τ r
    linarith

/-- **Unclassified-Contig Purity Sandwich Theorem**:
For *any* true completion `τ'` that classifies every contig in `B` at rank `r` and agrees
with `τ` on every already-classified contig, the true purity `purityCons B len τ' r` is
strictly sandwiched between `purityCons B len τ r` and `purityOpt B len τ r`, with interval
width equal to the unclassified base-pair fraction `unclassifiedLen / totalLen`. -/
theorem purity_unclassified_sandwich (B : Finset Contig) (len : Contig → ℕ)
    (τ τ' : Contig → TaxRank → Option Taxon) (r : TaxRank)
    (htot : 0 < totalLen B len)
    (hagree : ∀ c ∈ B, ∀ t, τ c r = some t → τ' c r = some t) :
    purityCons B len τ r ≤ purityCons B len τ' r ∧
    purityCons B len τ' r ≤ purityOpt B len τ r ∧
    purityOpt B len τ r - purityCons B len τ r = unclassifiedLen B len τ r / totalLen B len := by
  have hne : totalLen B len ≠ 0 := ne_of_gt htot
  -- Lower bound: `maxTaxonWeight τ ≤ maxTaxonWeight τ'`
  have hlow_w : maxTaxonWeight B len τ r ≤ maxTaxonWeight B len τ' r := by
    rw [maxTaxonWeight_le_iff B len τ r (maxTaxonWeight_nonneg B len τ' r)]
    intro t
    have htw : taxonWeight B len τ r t ≤ taxonWeight B len τ' r t := by
      unfold taxonWeight
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro c hc
        simp only [Finset.mem_filter] at hc ⊢
        exact ⟨hc.1, hagree c hc.1 t hc.2⟩
      · intro _ _ _; positivity
    exact le_trans htw (taxonWeight_le_maxTaxonWeight B len τ' r t)
  -- Upper bound: `maxTaxonWeight τ' ≤ maxTaxonWeight τ + unclassifiedLen τ`
  have hhigh_w : maxTaxonWeight B len τ' r ≤ maxTaxonWeight B len τ r + unclassifiedLen B len τ r := by
    have hnn : 0 ≤ maxTaxonWeight B len τ r + unclassifiedLen B len τ r :=
      add_nonneg (maxTaxonWeight_nonneg B len τ r) (totalLen_nonneg _ _)
    rw [maxTaxonWeight_le_iff B len τ' r hnn]
    intro t
    have hsub : B.filter (fun c => τ' c r = some t) ⊆
        B.filter (fun c => τ c r = some t) ∪ unclassifiedAt B τ r := by
      intro c hc
      simp only [Finset.mem_union, Finset.mem_filter, unclassifiedAt] at hc ⊢
      cases htc : τ c r with
      | none => right; exact ⟨hc.1, by simp⟩
      | some t₀ =>
        have heq : some t₀ = some t := by
          have := hagree c hc.1 t₀ htc
          rw [hc.2] at this
          exact this.symm
        injection heq with ht0
        subst ht0
        left
        exact ⟨hc.1, rfl⟩
    have hsum_le : taxonWeight B len τ' r t ≤
        taxonWeight B len τ r t + unclassifiedLen B len τ r := by
      unfold taxonWeight unclassifiedLen totalLen
      calc ∑ c ∈ B.filter (fun c => τ' c r = some t), (len c : ℚ)
          ≤ ∑ c ∈ B.filter (fun c => τ c r = some t) ∪ unclassifiedAt B τ r, (len c : ℚ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ ≤ (∑ c ∈ B.filter (fun c => τ c r = some t), (len c : ℚ)) +
              ∑ c ∈ unclassifiedAt B τ r, (len c : ℚ) := by
            have hui := Finset.sum_union_inter
              (s₁ := B.filter (fun c => τ c r = some t))
              (s₂ := unclassifiedAt B τ r) (f := fun c => (len c : ℚ))
            have hinter : 0 ≤ ∑ c ∈ B.filter (fun c => τ c r = some t) ∩ unclassifiedAt B τ r,
                (len c : ℚ) := Finset.sum_nonneg (fun _ _ => by positivity)
            linarith
    linarith [taxonWeight_le_maxTaxonWeight B len τ r t]
  refine ⟨?_, ?_, ?_⟩
  · unfold purityCons
    simp only [hne, ↓reduceIte]
    exact div_le_div_of_nonneg_right hlow_w (le_of_lt htot)
  · unfold purityCons purityOpt
    simp only [hne, ↓reduceIte]
    exact div_le_div_of_nonneg_right hhigh_w (le_of_lt htot)
  · unfold purityCons purityOpt
    simp only [hne, ↓reduceIte]
    ring

/-- **Rank-Refinement Monotonicity Theorem**:
Under tree-coherent contig taxonomic assignments (`TaxCoherent B τ`), descending from
a coarser rank `r₁` to a finer rank `r₂` (`r₁ ≤ r₂`) never increases dominant clade weight
or conservative purity, and never decreases conservative chimerism! -/
theorem rank_refinement_monotonicity (B : Finset Contig) (len : Contig → ℕ)
    (τ : Contig → TaxRank → Option Taxon) (hcoh : TaxCoherent B τ)
    {r₁ r₂ : TaxRank} (hr : r₁ ≤ r₂) :
    maxTaxonWeight B len τ r₂ ≤ maxTaxonWeight B len τ r₁ ∧
    purityCons B len τ r₂ ≤ purityCons B len τ r₁ ∧
    chimerismScore B len τ r₁ ≤ chimerismScore B len τ r₂ := by
  have hmax : maxTaxonWeight B len τ r₂ ≤ maxTaxonWeight B len τ r₁ := by
    rw [maxTaxonWeight_le_iff B len τ r₂ (maxTaxonWeight_nonneg B len τ r₁)]
    intro t₂
    by_cases hne : (B.filter (fun c => τ c r₂ = some t₂)).Nonempty
    · rcases hne with ⟨c₀, hc₀⟩
      simp only [Finset.mem_filter] at hc₀
      have hsome1 : (τ c₀ r₁).isSome := hcoh.prefix_closed c₀ hc₀.1 r₁ r₂ hr (by simp [hc₀.2])
      rcases Option.isSome_iff_exists.mp hsome1 with ⟨t₁, ht₁⟩
      have hsub : B.filter (fun c => τ c r₂ = some t₂) ⊆ B.filter (fun c => τ c r₁ = some t₁) := by
        intro c hc
        simp only [Finset.mem_filter] at hc ⊢
        refine ⟨hc.1, ?_⟩
        rw [hcoh.tree_consistent c hc.1 c₀ hc₀.1 r₁ r₂ t₂ hr hc.2 hc₀.2, ht₁]
      have hw : taxonWeight B len τ r₂ t₂ ≤ taxonWeight B len τ r₁ t₁ := by
        unfold taxonWeight
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      exact le_trans hw (taxonWeight_le_maxTaxonWeight B len τ r₁ t₁)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      unfold taxonWeight
      rw [hne, Finset.sum_empty]
      exact maxTaxonWeight_nonneg B len τ r₁
  have hpurity : purityCons B len τ r₂ ≤ purityCons B len τ r₁ := by
    unfold purityCons
    split_ifs with h0
    · exact le_refl 0
    · have hpos : 0 < totalLen B len := lt_of_le_of_ne (totalLen_nonneg B len) (Ne.symm h0)
      exact div_le_div_of_nonneg_right hmax (le_of_lt hpos)
  refine ⟨hmax, hpurity, ?_⟩
  unfold chimerismScore
  linarith

/-- **Closing the Stealth-Chimera Loophole**:
If a bin `B = B₁ ∪ B₂` (disjoint) merges two positive-length sub-bins belonging to
distinct clades `t₁ ≠ t₂` at rank `r`, then even if marker-based contamination is `0`,
conservative purity is strictly `< 1` and equals `max W₁ W₂ / (W₁ + W₂)`, forcing
chimerism score `= min W₁ W₂ / (W₁ + W₂) > 0`. -/
theorem taxonomic_catches_stealth_chimera
    {B₁ B₂ : Finset Contig} (hdisj : Disjoint B₁ B₂)
    (len : Contig → ℕ) (τ : Contig → TaxRank → Option Taxon) (r : TaxRank)
    {t₁ t₂ : Taxon} (hne : t₁ ≠ t₂)
    (h1 : ∀ c ∈ B₁, τ c r = some t₁)
    (h2 : ∀ c ∈ B₂, τ c r = some t₂)
    (hW₁ : 0 < totalLen B₁ len) (hW₂ : 0 < totalLen B₂ len) :
    let W₁ := totalLen B₁ len
    let W₂ := totalLen B₂ len
    purityCons (B₁ ∪ B₂) len τ r = max W₁ W₂ / (W₁ + W₂) ∧
    purityCons (B₁ ∪ B₂) len τ r < 1 ∧
    chimerismScore (B₁ ∪ B₂) len τ r = min W₁ W₂ / (W₁ + W₂) ∧
    0 < chimerismScore (B₁ ∪ B₂) len τ r := by
  intro W₁ W₂
  have htot : totalLen (B₁ ∪ B₂) len = W₁ + W₂ := by
    unfold W₁ W₂ totalLen
    exact Finset.sum_union hdisj
  have htot_pos : 0 < W₁ + W₂ := by linarith
  have htot_ne : totalLen (B₁ ∪ B₂) len ≠ 0 := by rw [htot]; exact ne_of_gt htot_pos
  have hf1 : (B₁ ∪ B₂).filter (fun c => τ c r = some t₁) = B₁ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hc | hc, hτ⟩
      · exact hc
      · rw [h2 c hc] at hτ
        injection hτ with ht
        exact absurd ht.symm hne
    · intro hc
      exact ⟨Or.inl hc, h1 c hc⟩
  have hf2 : (B₁ ∪ B₂).filter (fun c => τ c r = some t₂) = B₂ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hc | hc, hτ⟩
      · rw [h1 c hc] at hτ
        injection hτ with ht
        exact absurd ht hne
      · exact hc
    · intro hc
      exact ⟨Or.inr hc, h2 c hc⟩
  have hw1 : taxonWeight (B₁ ∪ B₂) len τ r t₁ = W₁ := by
    unfold taxonWeight W₁ totalLen; rw [hf1]
  have hw2 : taxonWeight (B₁ ∪ B₂) len τ r t₂ = W₂ := by
    unfold taxonWeight W₂ totalLen; rw [hf2]
  have hmax : maxTaxonWeight (B₁ ∪ B₂) len τ r = max W₁ W₂ := by
    apply le_antisymm
    · rw [maxTaxonWeight_le_iff _ _ _ _ (le_trans (le_of_lt hW₁) (le_max_left W₁ W₂))]
      intro t
      by_cases ht1 : t = t₁
      · subst ht1; rw [hw1]; exact le_max_left W₁ W₂
      · by_cases ht2 : t = t₂
        · subst ht2; rw [hw2]; exact le_max_right W₁ W₂
        · have hempty : (B₁ ∪ B₂).filter (fun c => τ c r = some t) = ∅ := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_union, Finset.notMem_empty, iff_false, not_and]
            rintro (hc | hc) hτ
            · rw [h1 c hc] at hτ; injection hτ with h; exact ht1 h.symm
            · rw [h2 c hc] at hτ; injection hτ with h; exact ht2 h.symm
          unfold taxonWeight
          rw [hempty, Finset.sum_empty]
          exact le_trans (le_of_lt hW₁) (le_max_left W₁ W₂)
    · rw [max_le_iff]
      exact ⟨hw1 ▸ taxonWeight_le_maxTaxonWeight _ _ _ _ t₁,
             hw2 ▸ taxonWeight_le_maxTaxonWeight _ _ _ _ t₂⟩
  have hpurity : purityCons (B₁ ∪ B₂) len τ r = max W₁ W₂ / (W₁ + W₂) := by
    unfold purityCons
    rw [ite_eq_right_iff.mpr (fun h => absurd h htot_ne), hmax, htot]
  have hp_lt1 : purityCons (B₁ ∪ B₂) len τ r < 1 := by
    rw [hpurity, div_lt_one htot_pos, max_lt_iff]
    exact ⟨by linarith, by linarith⟩
  have hchim : chimerismScore (B₁ ∪ B₂) len τ r = min W₁ W₂ / (W₁ + W₂) := by
    unfold chimerismScore
    rw [hpurity]
    have hsum : max W₁ W₂ + min W₁ W₂ = W₁ + W₂ := max_add_min W₁ W₂
    have hne' : W₁ + W₂ ≠ 0 := ne_of_gt htot_pos
    field_simp [hne']
    linarith
  have hchim_pos : 0 < chimerismScore (B₁ ∪ B₂) len τ r := by
    unfold chimerismScore; linarith
  exact ⟨hpurity, hp_lt1, hchim, hchim_pos⟩

end ContigPurity

/-- **Unclassified-Contig Dilution Counterexample**:
There exists a tree-coherent 2-contig chimeric bin (equal length contigs from two
distinct phyla, where the second contig is unclassified at Genus level) whose
`purityDrop` jumps from `1/2` at Phylum to `1` at Genus—while `purityCons` stays
honestly at `1/2`! -/
theorem unclassified_dilution_counterexample :
    ∃ (B : Finset (Fin 2)) (len : Fin 2 → ℕ) (τ : Fin 2 → TaxRank → Option ℕ),
      TaxCoherent B τ ∧
      purityDrop B len τ .phylum = 1 / 2 ∧
      purityDrop B len τ .genus = 1 ∧
      purityCons B len τ .phylum = 1 / 2 ∧
      purityCons B len τ .genus = 1 / 2 := by
  let B : Finset (Fin 2) := Finset.univ
  let len : Fin 2 → ℕ := fun _ => 50000
  let τ : Fin 2 → TaxRank → Option ℕ := fun c r =>
    if c = 0 then
      match r with
      | .domain => some 1
      | .phylum => some 10
      | .class_ => some 100
      | .order  => some 1000
      | .family => some 10000
      | .genus  => some 100000
      | .species => some 1000000
    else
      match r with
      | .domain => some 1
      | .phylum => some 20
      | _       => none
  have htot : totalLen B len = 100000 := by
    simp [totalLen, B, len]
    norm_num
  have hcl_p : classifiedLen B len τ .phylum = 100000 := by
    have hfilt : classifiedAt B τ .phylum = Finset.univ := by
      ext c; fin_cases c <;> simp [classifiedAt, B, τ]
    simp [classifiedLen, hfilt, totalLen, len]
    norm_num
  have hcl_g : classifiedLen B len τ .genus = 50000 := by
    have hfilt : classifiedAt B τ .genus = {0} := by
      ext c; fin_cases c <;> simp [classifiedAt, B, τ]
    simp [classifiedLen, hfilt, totalLen, len]
  have hmax_p : maxTaxonWeight B len τ .phylum = 50000 := by
    apply le_antisymm
    · rw [maxTaxonWeight_le_iff B len τ .phylum (by norm_num)]
      intro t
      by_cases ht10 : t = 10
      · subst ht10
        have hf : B.filter (fun c => τ c .phylum = some 10) = {0} := by
          ext c; fin_cases c <;> simp [B, τ]
        simp [taxonWeight, hf, len]
      · by_cases ht20 : t = 20
        · subst ht20
          have hf : B.filter (fun c => τ c .phylum = some 20) = {1} := by
            ext c; fin_cases c <;> simp [B, τ]
          simp [taxonWeight, hf, len]
        · have hf : B.filter (fun c => τ c .phylum = some t) = ∅ := by
            ext c; fin_cases c <;> simp [B, τ, Ne.symm ht10, Ne.symm ht20]
          simp [taxonWeight, hf]
    · have hw10 : taxonWeight B len τ .phylum 10 = 50000 := by
        have hf : B.filter (fun c => τ c .phylum = some 10) = {0} := by
          ext c; fin_cases c <;> simp [B, τ]
        simp [taxonWeight, hf, len]
      exact hw10 ▸ taxonWeight_le_maxTaxonWeight B len τ .phylum 10
  have hmax_g : maxTaxonWeight B len τ .genus = 50000 := by
    apply le_antisymm
    · rw [maxTaxonWeight_le_iff B len τ .genus (by norm_num)]
      intro t
      by_cases ht : t = 100000
      · subst ht
        have hf : B.filter (fun c => τ c .genus = some 100000) = {0} := by
          ext c; fin_cases c <;> simp [B, τ]
        simp [taxonWeight, hf, len]
      · have hf : B.filter (fun c => τ c .genus = some t) = ∅ := by
          ext c; fin_cases c <;> simp [B, τ, Ne.symm ht]
        simp [taxonWeight, hf]
    · have hw : taxonWeight B len τ .genus 100000 = 50000 := by
        have hf : B.filter (fun c => τ c .genus = some 100000) = {0} := by
          ext c; fin_cases c <;> simp [B, τ]
        simp [taxonWeight, hf, len]
      exact hw ▸ taxonWeight_le_maxTaxonWeight B len τ .genus 100000
  refine ⟨B, len, τ, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro c _ r₁ r₂ hr hsome
      fin_cases c
      · cases r₁ <;> simp [τ]
      · cases r₂
        · cases r₁ <;> simp_all [τ, TaxRank.le_iff_toNat_le, TaxRank.toNat]
        · cases r₁ <;> simp_all [τ, TaxRank.le_iff_toNat_le, TaxRank.toNat]
        · simp [τ] at hsome
        · simp [τ] at hsome
        · simp [τ] at hsome
        · simp [τ] at hsome
        · simp [τ] at hsome
    · intro c₁ _ c₂ _ r₁ r₂ t hr h1 h2
      by_cases hceq : c₁ = c₂
      · subst hceq; rfl
      · have hr2_dom : r₂ = .domain := by
          fin_cases c₁ <;> fin_cases c₂
          · exact absurd rfl hceq
          · cases r₂ <;> simp [τ] at h1 h2 <;> try omega
            rfl
          · cases r₂ <;> simp [τ] at h1 h2 <;> try omega
            rfl
          · exact absurd rfl hceq
        subst hr2_dom
        have hr1_dom : r₁ = .domain := by
          cases r₁ <;> simp [TaxRank.le_iff_toNat_le, TaxRank.toNat] at hr <;> rfl
        subst hr1_dom
        fin_cases c₁ <;> fin_cases c₂ <;> simp [τ]
  · simp [purityDrop, hcl_p, hmax_p]; norm_num
  · simp [purityDrop, hcl_g, hmax_g]
  · simp [purityCons, htot, hmax_p]; norm_num
  · simp [purityCons, htot, hmax_g]; norm_num

end MAGLean.Taxonomy
