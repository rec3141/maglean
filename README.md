# MAGLean — Formal Verification & Mathematical Guarantees for Metagenome-Assembled Genomes

**MAGLean** is a Lean 4 + Mathlib formalization of quality-control (QC) metrics for Metagenome-Assembled Genomes (MAGs), paired with a compiled native command-line auditor (`maglean`) and a strict converter from real bioinformatics tool outputs.

Rather than treating completeness, contamination, chimerism, taxonomic placement, MIMAG tiers, and ANI dereplication as ad-hoc pipeline heuristics, MAGLean states them as definitions and **machine-checked theorems about those definitions** (zero `sorry`; all 59 flagship theorems listed in `Tests/AxiomAudit.lean` depend exclusively on Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`), paired with an exact-rational (`Rat`) CLI auditor whose core computations are linked to the formal theory by bridge theorems in `MAGLean/Certificate.lean`. See [What a report attests](#what-a-report-attests).

---

## Architecture

| Layer | Modules | Purpose |
| :--- | :--- | :--- |
| **Core Algebra** | `MAGLean/Basic.lean`, `MAGLean/Markers.lean` | Collocated single-copy marker families (CheckM model), exact marker-mass conservation, chimeric masking, disjoint-support zero-contamination construction, core-vs-accessory blindness, strain heterogeneity, and pair-vs-excess discrepancy theorems. |
| **Statistical Bounds** | `MAGLean/Probabilistic.lean` | First-principles proof of Bernoulli and general bounded `[0, 1]` Hoeffding's Lemma, exact variance & Chebyshev bounds, two-sided exponential Hoeffding concentration bounds (both equal-weight Bernoulli and general weighted `[0, 1]` / contig-level models), sample-size bounds, and chimeric masking expectations. |
| **Taxonomic Hierarchy** | `MAGLean/Taxonomy.lean` | Rooted clade hierarchies (LCA semilattice), DPANN/Patescibacteria lineage-loss ceilings, safe LCA rank selection, whole-contig rank purity (distinct from GUNC's gene-level conditional entropy `CSS`), unclassified-contig dilution counterexamples, and two-clade stealth-chimera detection. |
| **Standards & Scores** | `MAGLean/Quality.lean` | Exhaustive, mutually exclusive MIMAG draft + contaminated classification (Bowers et al., 2017 cutoffs), HQ-to-MQ RNA downgrade, linear composite score `Q_α = Comp - α·Cont` chimera-incentive thresholds (Parks `Q_5`), and purity-gated scoring. |
| **Dereplication (ANI/AF)** | `MAGLean/Dereplication.lean` | Constructive ANI triangle-inequality failure, overlap-conditioned relaxed triangle inequality (`AF₁₂ + AF₂₃ > 1`), and star-cluster diameter bounds on a shared gapless reference coordinate set. |
| **Metagenome Binning** | `MAGLean/Binning.lean` | Single-valued `BinMap` disjointness, assembly base-pair additivity, single-family marker-mass additivity across bins + unbinned contigs, and QC-gated bin filtering. |
| **Executable CLI & Provenance** | `MAGLean/Sha256.lean`, `MAGLean/Kernel.lean`, `MAGLean/Certificate.lean`, `Main.lean` | Zero-Mathlib native CLI binary (`maglean`) with exact rational arithmetic, pure-Lean SHA-256 input hashing, baked-in build/toolchain provenance, and machine-checked bridge theorems in `Certificate.lean`. |
| **Tool Converter** | `scripts/convert_evidence.py` | Strict Python converter (outside the verified kernel) from CheckM `marker_gene_stats.tsv`, contig taxonomy TSV, barrnap GFF3, and tRNAscan-SE TSV to MAGLean JSON, with real genome (`GCF_000005845.2`) and MAG (`UBA10002`) test fixtures. |

---

## Flagship Proven Theorems

### 1. Completeness, Contamination, Conservation & Strain Heterogeneity (`MAGLean/Markers.lean`)
- **`comp_add_cont_eq_mass` & `conservation_law`**: Total weighted marker copy mass satisfies `Comp(B) + Cont(B) = MarkerMass(B)` and is strictly additive across disjoint contig unions:
  $$\text{Comp}(B_1 \sqcup B_2) + \text{Cont}(B_1 \sqcup B_2) = (\text{Comp}(B_1) + \text{Cont}(B_1)) + (\text{Comp}(B_2) + \text{Cont}(B_2))$$
- **`cont_add_eq` & `comp_add_eq`**: Merging $B_1$ and $B_2$ creates exact cross-contamination equal to `sharedCompleteness(B₁, B₂)`, and reduces combined completeness relative to `Comp(B₁) + Comp(B₂)` by the exact same quantity.
- **`split_completeness_ceiling`**: De-chimerizing a bin $B$ into $B_1 \sqcup B_2$ can recover at most `Comp(B) + Cont(B)` in total completeness.
- **`stealth_chimera_exists`**: For every marker family with at least two distinct markers, there exist two marker-count profiles with disjoint support, positive completeness, and zero marker contamination whose sum scores **100% completeness and 0% contamination**.
- **`accessory_invariance`**: Adding or removing arbitrary marker-free contigs (plasmids, prophages, accessory islands) leaves `Comp` and `Cont` strictly unchanged.
- **`nonStrainContamination_pair_weighting_discrepancy` & `nonStrainContamination_exact_for_double_copies`**: Proves that `cont * (1 - SH)` strictly underestimates inter-species excess contamination when a marker has $\ge 3$ copies (because `SH` weights by pairs $\binom{n}{2}$ while contamination weights linearly by $n - 1$: e.g., 3 identical strain copies + 2 inter-species copies yields `3/8 = 0.375` vs. true `1/2 = 0.5`), AND proves that `cont * (1 - SH)` *is* exact when all multi-copy markers have at most 2 copies on equally weighted singletons.

### 2. Finite-Sample Statistical Bounds (`MAGLean/Probabilistic.lean`)
- **`hoeffding_lemma_bernoulli` & `hoeffding_lemma_bounded`**: First-principles calculus proof of `(1 - p)e^{-pt} + p e^{(1-p)t} ≤ e^{t^2/8}`, lifted to arbitrary finite-support `[0, 1]`-valued random variables (covering fractional multi-gene collocated sets).
- **`hoeffding_completeness_bound`**: For the mean of $k$ independent Bernoulli observations with common detection probability $p$, $\Pr(|\widehat{p}_k - p| \ge \varepsilon) \le 2 e^{-2 k \varepsilon^2}$.
- **`hoeffding_weighted_bounded`**: General weighted Hoeffding inequality $\Pr(|S - \mathbb{E}[S]| \ge \varepsilon) \le 2 e^{-2 \varepsilon^2 / \sum a_j^2}$ for independent `[0, 1]`-valued observations with arbitrary means and weights (covering both fractional collocated marker sets and independent contig-level weights).
- **`marker_count_sufficient` & `hoeffdingRadius_strict_shrink`**: Certified sample-size formula $k \ge \frac{\ln(2/\delta)}{2\varepsilon^2}$ and strict monotonicity of `hoeffdingRadius` in $k$.
- **`single_marker_chimeric_expectation` & `mimag_mq_evasion_expectation`**: Under independent target ($p$) and contaminant ($q$), $\mathbb{E}[\text{Comp}_{\text{obs}}] = p + q - pq$ and $\mathbb{E}[\text{Cont}_{\text{obs}}] = pq$ (50% target + 18% contaminant → 59% apparent completeness, 9% contamination).

### 3. Taxonomic Hierarchy & Contig-Level Purity (`MAGLean/Taxonomy.lean`)
- **`lineage_loss_bias_bound` & `lineage_loss_exact_complete`**: A reduced-genome clade (e.g. Patescibacteria / DPANN / symbionts) missing fraction $\lambda$ of ancestral markers has apparent ancestral completeness capped at $1 - \lambda$ even when 100% biologically complete.
- **`lca_zero_lineage_loss`**: Evaluating a MAG with phylogenetic placement uncertainty set $U$ at $\text{LCA}(U)$ guarantees zero lineage-loss bias across all $v \in U$.
- **Scope vs. GUNC (`Orakov et al., 2021`)**: Purity and chimerism here take at most one taxon per contig per rank (`Contig → TaxRank → Option Taxon`), weighted by contig base pairs—modeling whole-contig classifiers rather than GUNC's gene-level conditional taxonomic entropy (`CSS`) or reference representation score (`RRS`).
- **`rank_refinement_monotonicity`**: Under tree-coherent contig taxonomy (`TaxCoherent`), conservative purity is monotonically non-increasing (and chimerism non-decreasing) from Domain to Species.
- **`purity_unclassified_sandwich`**: For *any* completion of unclassified contigs agreeing with existing contig calls, full-bin purity lies inside `[purityCons, purityOpt]`, with width equal to the unclassified bp fraction.
- **`unclassified_dilution_counterexample`**: Explicit tree-coherent chimeric bin whose drop-unclassified purity jumps artificially from `50%` (Phylum) to `100%` (Genus).
- **`taxonomic_catches_stealth_chimera`**: Merging two disjoint sub-bins of positive base-pair length ($W_1 > 0, W_2 > 0$) uniformly labelled with distinct clades $t_1 \ne t_2$ at rank $r$ forces conservative purity $\frac{\max(W_1, W_2)}{W_1 + W_2} < 1$.

### 4. MIMAG Standards & Composite Scores (`MAGLean/Quality.lean`)
- **`mimag_partition_unique`**: Exact rational classification into four exhaustive, mutually exclusive tiers (`HQ`, `MQ`, `LQ`, `Contaminated`), matching the numerical completeness/contamination inequalities of Bowers et al. (2017) Table 1 plus explicit `Cont ≥ 10%` (`Finished` and assembly-gap criteria are not modeled).
- **`mimag_hq_downgrade_missing_rna`**: Proves strict downgrade from HQ to MQ when `RNAProfile` fails (`23S`, `16S`, `5S`, and `distinctTRNAs ≥ 18` standard amino-acid isotypes).
- **`compositeScore_chimera_incentive` & `drep_Q5_chimera_threshold`**: Adding fragment $c$ strictly increases linear $Q_\alpha = \text{Comp} - \alpha \cdot \text{Cont}$ iff $\text{Comp}(c) > (\alpha + 1)\cdot\text{Shared}(f, c) + \alpha\cdot\text{Cont}(c)$. For Parks et al.'s linear $Q_5$ and zero-contamination $c$, $Q_5$ increases whenever $\text{Shared}(f, c) < \text{Comp}(c) / 6$.

### 5. ANI Dereplication (`MAGLean/Dereplication.lean`)
- **Model scope**: Genomes are modeled as single-copy functions `Locus → Base` over one shared gapless reference coordinate set `S` with `AF = |A| / |S|`.
- **`ani_triangle_inequality_counterexample`**: Constructive 3-genome counterexample (`AF = 50%`, `ANI₁₂ = ANI₂₃ = 100%`, `ANI₁₃ = 0%`).
- **`ani_core_overlap_theorem`**, **`derep_cluster_diameter_bound`**, **`derep_80_97_corollary`**: Whenever $\text{AF}_{12} + \text{AF}_{23} > 1$, the mutual core covers at least $\text{AF}_{12} + \text{AF}_{23} - 1$ of $S$ with core identity $\ge 1 - \frac{\text{AF}_{12}(1 - \text{ANI}_{12}) + \text{AF}_{23}(1 - \text{ANI}_{23})}{\text{AF}_{12} + \text{AF}_{23} - 1}$ (e.g., `AF ≥ 80%` and `ANI ≥ 97%` to representative guarantees `≥ 60%` shared core at `≥ 92%` core ANI).

### 6. Metagenome Binning (`MAGLean/Binning.lean`)
- **`binOf_disjoint`**, **`assembly_length_conservation`**, **`global_metagenome_marker_conservation`**, **`filterValidBins_sound`**: Partition disjointness, base-pair additivity, single-family marker-mass conservation across bins + unbinned contigs, and threshold soundness of QC-gated bin filtering.

---

## What a report attests

Every CLI report (text and `--json`) embeds **reproducible provenance**: the exact SHA-256 hash of the input file bytes (`input_sha256`), the MAGLean version (`maglean_version`), the git commit baked into the binary at build time (`git_commit`), and the Lean compiler toolchain (`lean_toolchain`).

Report fields whose executable `MAGLean.Kernel` function has a **machine-checked bridge theorem** in `MAGLean/Certificate.lean` (audited in `Tests/AxiomAudit.lean`):

| Report field | Bridge theorem(s) | What it establishes |
| :--- | :--- | :--- |
| Completeness | `kCompleteness_eq_completeness`, `binMarkerCount_eq_binCounts` | Exact equality with `Markers.completeness` on the deduplicated marker family and contig-aggregated hit counts. |
| Contamination | `kContamination_eq_contamination`, `binMarkerCount_eq_binCounts` | Exact equality with `Markers.contamination`. |
| Total Marker Mass & Split Ceiling | `kMarkerMass_eq_markerMass`, `kCompleteness_add_kContamination_eq_kMarkerMass` | Exact equality with `Markers.markerMass` and exact conservation `comp + cont = mass` (`Markers.split_completeness_ceiling`). |
| Composite `Q_5` | `kCompositeQ5_eq_compositeScore` | Exact equality with `Quality.compositeScore 5`. |
| MIMAG Tier | `kClassifyMIMAG_eq_classifyMIMAG` | Exact agreement with `Quality.classifyMIMAG` (`Quality.mimag_partition_unique`). |
| Strain Heterogeneity | `kStrainHeterogeneity_eq`, `kNonStrainCont_eq` | Exact agreement with `Markers.strainHeterogeneity` and `Markers.nonStrainContamination` (which is exact for inter-species excess only when multi-copy markers have `≤ 2` copies, per `nonStrainContamination_pair_weighting_discrepancy`). |
| Tree Coherence | `kCheckTaxCoherent_sound` | Directly proves that `Kernel.kCheckTaxCoherent contigs = true` (with unique contig IDs) implies `Taxonomy.TaxCoherent`, unlocking `Taxonomy.rank_refinement_monotonicity`. |
| Rank Purity & Chimerism Table | `kRankAudit_eq_taxonomy` | Exact equality of all five rational columns (`purityCons`, `purityOpt`, `purityDrop`, `chimerism`, `unclassifiedFrac`) with the `MAGLean.Taxonomy` definitions. |
| `STEALTH_CHIMERA_ALERT` threshold | `kRankAudit_stealth_alert_sound` | Whenever `purityOpt < 9/10` at some rank on a positive-length bin, *every* completion of unclassified contigs agreeing with classified contigs has full-bin purity `< 9/10`. |
| Hoeffding CI radius | `kernel_hoeffding95_sound` | For `k ≥ 2`, the exact rational radius (`hoeffding_95_radius_exact`) satisfies the ≥ 95% Hoeffding bound under the independent observation model. Because marker-set independence is an unverified biological assumption, the marker-set CI is omitted from the default text report unless `--ci` is passed. |

Still outside the formal theorems: the JSON parser (`parseMAGEvidence`), SHA-256 implementation (`Sha256.lean`, tested against Python `hashlib.sha256`), `auditMAG` control flow, percentage string truncation (`formatPercent`), accessory-contig count display, the remaining text alerts, and the external Python converter (`scripts/convert_evidence.py`).

---

## Building & Running

### 1. Build the Formal Theory Library & Native CLI
```bash
lake build MAGLean
lake build maglean
```

### 2. Run the Axiom Audit (59 Flagship Theorems, Standard Axioms Only)
```bash
lake env lean Tests/AxiomAudit.lean
```

### 3. Run the MAG QC Auditor
```bash
# Default text report (with SHA-256 provenance and contig-level Hoeffding radius)
.lake/build/bin/maglean examples/hq_ecoli_mag.json examples/stealth_chimera_mag.json

# Include conditional independent-marker-set Hoeffding CI in text output
.lake/build/bin/maglean --ci examples/hq_ecoli_mag.json

# Machine-readable JSON report
.lake/build/bin/maglean --json examples/unclassified_dilution_mag.json
```

### 4. Convert Real Tool Outputs (CheckM + Contig Taxonomy + barrnap + tRNAscan-SE)
```bash
python3 scripts/convert_evidence.py \
  --mag-id GCF_000005845.2_Ecoli_MG1655 \
  --lineage "d__Bacteria;p__Pseudomonadota;c__Gammaproteobacteria;o__Enterobacterales;f__Enterobacteriaceae;g__Escherichia;s__Escherichia coli" \
  --contigs examples/real_tool_outputs/ecoli_mg1655/contigs.tsv \
  --marker-sets examples/real_tool_outputs/bacterial_markers.tsv \
  --checkm-hits examples/real_tool_outputs/ecoli_mg1655/checkm_marker_gene_stats.tsv \
  --bin-id GCF_000005845.2 \
  --taxonomy examples/real_tool_outputs/ecoli_mg1655/contig_taxonomy.tsv \
  --barrnap examples/real_tool_outputs/ecoli_mg1655/barrnap.gff \
  --trnascan examples/real_tool_outputs/ecoli_mg1655/trnascan.tsv \
  -o /tmp/ecoli_mg1655.json

.lake/build/bin/maglean /tmp/ecoli_mg1655.json
```

### 5. Run All 14 Automated CLI, Provenance, Regression & Converter Tests
```bash
python3 Tests/run_cli_tests.py
```
