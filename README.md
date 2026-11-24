# MAGLean — Formal Verification & Mathematical Guarantees for Metagenome-Assembled Genomes

**MAGLean** is a Lean 4 + Mathlib formalization and proof-carrying quality-control (QC) auditor for Metagenome-Assembled Genomes (MAGs).

Rather than treating completeness, contamination, chimerism, taxonomic placement, MIMAG tiers, and ANI dereplication as ad-hoc pipeline heuristics, MAGLean turns them into **machine-checked mathematical contracts** (zero `sorry`, zero custom axioms) paired with a fast, compiled native QC auditor (`maglean`) using exact rational arithmetic (`Rat`).

---

## Architecture

| Layer | Modules | Purpose |
| :--- | :--- | :--- |
| **Core Algebra** | `MAGLean/Basic.lean`, `MAGLean/Markers.lean` | Collocated single-copy marker families (CheckM model), exact marker-mass conservation, chimeric masking, stealth-chimera impossibility, core-vs-accessory blindness, and strain heterogeneity. |
| **Statistical Bounds** | `MAGLean/Probabilistic.lean` | First-principles proof of Bernoulli Hoeffding's Lemma, exact variance & Chebyshev bounds, two-sided exponential Hoeffding concentration bounds, sample-size certification, and chimeric masking expectations. |
| **Taxonomic Hierarchy** | `MAGLean/Taxonomy.lean` | Rooted clade hierarchies (LCA semilattice), DPANN/Patescibacteria lineage-loss ceilings, safe LCA rank selection, whole-contig rank purity (distinct from GUNC's gene-level conditional entropy `CSS`), unclassified-contig dilution counterexamples, and two-clade stealth-chimera detection. |
| **Standards & Scores** | `MAGLean/Quality.lean` | Exhaustive, mutually exclusive MIMAG draft + contaminated classification (Bowers et al., 2017 cutoffs), HQ-to-MQ RNA downgrade, linear composite score `Q_α = Comp - α·Cont` chimera-incentive thresholds (Parks `Q_5`), and purity-gated scoring. |
| **Dereplication (ANI/AF)** | `MAGLean/Dereplication.lean` | Constructive ANI triangle-inequality failure, overlap-conditioned relaxed triangle inequality (`AF₁₂ + AF₂₃ > 1`), and star-cluster diameter bounds on a shared gapless reference coordinate set. |
| **Metagenome Binning** | `MAGLean/Binning.lean` | Single-valued `BinMap` disjointness, assembly base-pair additivity, single-family marker-mass additivity across bins + unbinned contigs, and QC-gated bin filtering. |
| **Verified Executable CLI** | `MAGLean/Kernel.lean`, `MAGLean/Certificate.lean`, `Main.lean` | Zero-Mathlib native CLI binary (`maglean`) with exact rational arithmetic and machine-checked soundness bridge theorems linking CLI outputs to the Mathlib theory. |

---

## Flagship Proven Theorems

### 1. Completeness, Contamination & Marker Algebra (`MAGLean/Markers.lean`)
- **`comp_add_cont_eq_mass` & `conservation_law`**: Total weighted marker copy mass satisfies `Comp(B) + Cont(B) = MarkerMass(B)` and is **strictly additive** across disjoint contig unions:
  $$\text{Comp}(B_1 \sqcup B_2) + \text{Cont}(B_1 \sqcup B_2) = (\text{Comp}(B_1) + \text{Cont}(B_1)) + (\text{Comp}(B_2) + \text{Cont}(B_2))$$
- **`cont_add_eq` & `comp_add_eq`**: Merging $B_1$ and $B_2$ creates *exact* cross-contamination equal to `sharedCompleteness(B₁, B₂)`, and reduces combined completeness relative to `Comp(B₁) + Comp(B₂)` by the exact same quantity.
- **`split_completeness_ceiling`**: De-chimerizing a bin $B$ into $B_1 \sqcup B_2$ can recover at most `Comp(B) + Cont(B)` in total completeness.
- **`stealth_chimera_exists`** proves that for every family with at least two distinct markers, there exist two marker-count profiles with disjoint support and positive completeness. Each has zero marker contamination, and their sum scores **100% marker completeness and 0% marker contamination**. These scores alone cannot distinguish the combined profile from one copy of every marker.
- **`accessory_invariance`**: Adding or removing arbitrary marker-free contigs (plasmids, prophages, accessory islands) leaves `Comp` and `Cont` strictly unchanged.

### 2. Finite-Sample Statistical Guarantees (`MAGLean/Probabilistic.lean`)
- **`hoeffding_lemma_bernoulli`**: First-principles calculus proof of `(1 - p)e^{-pt} + p e^{(1-p)t} ≤ e^{t^2/8}`.
- **`hoeffding_completeness_bound`**: For the mean of $k$ independent Bernoulli observations with common detection probability $p$, $\Pr(|\widehat{p}_k - p| \ge \varepsilon) \le 2 e^{-2 k \varepsilon^2}$.
- **`marker_count_sufficient` & `hoeffdingRadius_strict_shrink`**: Certified sample-size formula $k \ge \frac{\ln(2/\delta)}{2\varepsilon^2}$ under that model. At fixed confidence level, increasing $k$ strictly shrinks the radius. To apply it to a MAG, the marker observations must justify the model: genes within one set can be partially detected, and distinct sets can have correlated detections.
- **`single_marker_chimeric_expectation` & `mimag_mq_evasion_expectation`**: Under independent target ($p$) and contaminant ($q$), $\mathbb{E}[\text{Comp}_{\text{obs}}] = p + q - pq$ and $\mathbb{E}[\text{Cont}_{\text{obs}}] = pq$—proving that a 50%-complete bin + 18% foreign genome yields 59% apparent completeness and 9% contamination (passing MIMAG MQ in expectation).

### 3. Taxonomic Hierarchy & Contig-Level Purity (`MAGLean/Taxonomy.lean`)
- **`lineage_loss_bias_bound` & `lineage_loss_exact_complete`**: A reduced-genome clade (e.g. Patescibacteria / DPANN / symbionts) missing fraction $\lambda$ of ancestral markers has apparent ancestral completeness capped at $1 - \lambda$ even when 100% biologically complete.
- **`lca_zero_lineage_loss`**: Evaluating a MAG with phylogenetic placement uncertainty set $U$ at $\text{LCA}(U)$ guarantees zero lineage-loss bias across all $v \in U$.
- **Scope vs. GUNC (`Orakov et al., 2021`)**: Purity and chimerism here take at most one taxon per contig per rank (`Contig → TaxRank → Option Taxon`), weighted by contig base pairs. That models whole-contig taxonomic classifiers, not GUNC's gene-level conditional taxonomic entropy (`CSS`) or reference representation score (`RRS`).
- **`rank_refinement_monotonicity`**: Under tree-coherent contig taxonomy (`TaxCoherent`), conservative purity is monotonically non-increasing (and chimerism non-decreasing) from Domain to Species.
- **`purity_unclassified_sandwich`**: For *any* completion of unclassified contigs agreeing with existing contig calls, full-bin purity lies inside `[purityCons, purityOpt]`, with width equal to the unclassified bp fraction.
- **`unclassified_dilution_counterexample`**: Explicit tree-coherent chimeric bin whose drop-unclassified purity jumps artificially from `50%` (Phylum) to `100%` (Genus).
- **`taxonomic_catches_stealth_chimera`**: Merging two disjoint sub-bins of positive total base-pair length ($W_1 > 0, W_2 > 0$) uniformly labelled with distinct clades $t_1 \ne t_2$ at rank $r$ forces conservative purity $\frac{\max(W_1, W_2)}{W_1 + W_2} < 1$.

### 4. MIMAG Standards & Composite Scores (`MAGLean/Quality.lean`)
- **`mimag_partition_unique`**: Exact rational classification into four exhaustive, mutually exclusive tiers (`HQ`, `MQ`, `LQ`, `Contaminated`), matching the numerical completeness/contamination inequalities of Bowers et al. (2017) Table 1 and adding explicit `Cont ≥ 10%` (`Finished` and assembly-gap criteria are not modeled).
- **`mimag_hq_downgrade_missing_rna`**: Proves strict downgrade from HQ to MQ when `RNAProfile` fails (`23S`, `16S`, `5S`, and `distinctTRNAs ≥ 18`; to match Bowers et al. 2017, the caller must supply the count of distinct standard amino-acid tRNA isotypes rather than raw anticodon species).
- **`compositeScore_chimera_incentive` & `drep_Q5_chimera_threshold`**: Adding fragment $c$ strictly *increases* linear $Q_\alpha = \text{Comp} - \alpha \cdot \text{Cont}$ iff $\text{Comp}(c) > (\alpha + 1)\cdot\text{Shared}(f, c) + \alpha\cdot\text{Cont}(c)$. For Parks et al.'s linear $Q_5 = \text{Comp} - 5\cdot\text{Cont}$ and zero-contamination $c$, $Q_5$ increases whenever $\text{Shared}(f, c) < \text{Comp}(c) / 6$ (note that `dRep`'s default winner score also adds $+\,\text{Cont}\cdot(\text{SH}/100) + 0.5\log_{10}(\text{N50}) + (\text{centrality} - S_{\text{ani}})$, which lowers the effective contamination penalty toward $4$ on high-AAI strain merges).

### 5. ANI Dereplication (`MAGLean/Dereplication.lean`)
- **Model scope**: Genomes are modeled as single-copy functions `Locus → Base` over one shared gapless reference coordinate set `S` (the representative's loci), with `AF = |A| / |S|`. Pairwise local aligners (`fastANI`, `skani`, `ANIm`) instead filter out low-identity fragments and permit indels and repeats.
- **`ani_triangle_inequality_counterexample`**: Constructive 3-genome counterexample (`AF = 50%`, `ANI₁₂ = ANI₂₃ = 100%`, `ANI₁₃ = 0%`).
- **`ani_core_overlap_theorem`**: Under the shared-locus model, whenever $\text{AF}_{12} + \text{AF}_{23} > 1$ relative to $S$, the mutual core $A_{12} \cap A_{23}$ covers at least $\text{AF}_{12} + \text{AF}_{23} - 1$ of $S$ with core identity:
  $$\text{ANI}_{13}^{\text{core}} \ge 1 - \frac{\text{AF}_{12}(1 - \text{ANI}_{12}) + \text{AF}_{23}(1 - \text{ANI}_{23})}{\text{AF}_{12} + \text{AF}_{23} - 1}$$
- **`derep_cluster_diameter_bound` & `derep_80_97_corollary`**: Under star clustering where members align to representative $S$ at `AF ≥ 80%` and `ANI ≥ 97%`, every pair shares `≥ 60%` of $S$ with `≥ 92%` core ANI (note that `dRep`'s default secondary clustering uses average linkage at `S_ani = 0.95` and `cov_thresh = 0.10`, which does not enforce `AF > 50%`).

### 6. Metagenome Binning & Verified Filtering (`MAGLean/Binning.lean`)
- **`global_metagenome_marker_conservation`**: For a *single fixed* marker family $M$ and any fixed per-contig hit table, across any partition of assembly $A$ into bins $B_1, \dots, B_m$ plus unbinned contigs $U$, $\sum_b (\text{Comp}_M(B_b) + \text{Cont}_M(B_b)) + (\text{Comp}_M(U) + \text{Cont}_M(U)) = \text{Comp}_M(A) + \text{Cont}_M(A)$. This does not apply across `CheckM lineage_wf` outputs that choose a different lineage-specific marker family $M_b$ per bin, and matching CheckM's per-bin counts from raw ORF hits requires applying CheckM's per-scaffold adjacent-ORF merging consistently beforehand.
- **`filterValidBins_sound`**: Verified QC-gated bin selector preserving strict contig disjointness and guaranteeing every retained bin meets `(minComp, maxCont, minPurity)`.

---

## Building & Running

### 1. Build the Formal Theory Library & Native CLI
```bash
lake build MAGLean
lake build maglean
```

### 2. Run the Axiom Audit (Zero `sorry`, Standard Axioms Only)
```bash
lake env lean Tests/AxiomAudit.lean
```

### 3. Run the Proof-Carrying MAG QC Auditor
```bash
# Human-readable verified QC certificates
.lake/build/bin/maglean examples/hq_ecoli_mag.json examples/stealth_chimera_mag.json

# Machine-readable JSON certificate
.lake/build/bin/maglean --json examples/unclassified_dilution_mag.json

# Run full automated CLI test suite
python3 Tests/run_cli_tests.py
```
