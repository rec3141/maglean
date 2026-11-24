# MAGLean — Formal Verification & Mathematical Guarantees for Metagenome-Assembled Genomes

**MAGLean** is a Lean 4 + Mathlib formalization and proof-carrying quality-control (QC) auditor for Metagenome-Assembled Genomes (MAGs).

Rather than treating completeness, contamination, chimerism, taxonomic placement, MIMAG tiers, and ANI dereplication as ad-hoc pipeline heuristics, MAGLean turns them into **machine-checked mathematical contracts** (zero `sorry`, zero custom axioms) paired with a fast, compiled native QC auditor (`maglean`) using exact rational arithmetic (`Rat`).

---

## Architecture

| Layer | Modules | Purpose |
| :--- | :--- | :--- |
| **Core Algebra** | `MAGLean/Basic.lean`, `MAGLean/Markers.lean` | Collocated single-copy marker families (CheckM model), exact marker-mass conservation, chimeric masking, stealth-chimera impossibility, core-vs-accessory blindness, and strain heterogeneity. |
| **Statistical Bounds** | `MAGLean/Probabilistic.lean` | First-principles proof of Bernoulli Hoeffding's Lemma, exact variance & Chebyshev bounds, two-sided exponential Hoeffding concentration bounds, sample-size certification, and chimeric masking expectations. |
| **Taxonomic Hierarchy** | `MAGLean/Taxonomy.lean` | Rooted clade hierarchies (LCA semilattice), DPANN/Patescibacteria lineage-loss ceilings, safe LCA rank selection, GUNC-style rank purity, unclassified-contig dilution counterexamples, and stealth-chimera detection. |
| **Standards & Scores** | `MAGLean/Quality.lean` | Exhaustive, mutually exclusive MIMAG (Bowers et al., 2017) classification, HQ-to-MQ RNA downgrade, composite quality score `Q_α = Comp - α·Cont` chimera-incentive thresholds (including dRep/Parks `Q_5`), and purity-gated scoring. |
| **Dereplication (ANI/AF)** | `MAGLean/Dereplication.lean` | Constructive ANI triangle-inequality failure, overlap-conditioned relaxed triangle inequality (`AF₁₂ + AF₂₃ > 1`), and intra-cluster diameter bounds. |
| **Metagenome Binning** | `MAGLean/Binning.lean` | Zero-duplication binning invariants, assembly base-pair conservation, global metagenome marker-mass conservation across all bins + unbinned contigs, and verified QC-gated bin filtering. |
| **Verified Executable CLI** | `MAGLean/Kernel.lean`, `MAGLean/Certificate.lean`, `Main.lean` | Zero-Mathlib native CLI binary (`maglean`) with exact rational arithmetic and machine-checked soundness bridge theorems linking CLI outputs to the Mathlib theory. |

---

## Flagship Proven Theorems

### 1. Completeness, Contamination & Marker Algebra (`MAGLean/Markers.lean`)
- **`comp_add_cont_eq_mass` & `conservation_law`**: Total weighted marker copy mass satisfies `Comp(B) + Cont(B) = MarkerMass(B)` and is **strictly additive** across disjoint contig unions:
  $$\text{Comp}(B_1 \sqcup B_2) + \text{Cont}(B_1 \sqcup B_2) = (\text{Comp}(B_1) + \text{Cont}(B_1)) + (\text{Comp}(B_2) + \text{Cont}(B_2))$$
- **`cont_add_eq` & `comp_add_eq`**: Merging $B_1$ and $B_2$ creates *exact* cross-contamination equal to `sharedCompleteness(B₁, B₂)`, and reduces combined completeness relative to `Comp(B₁) + Comp(B₂)` by the exact same quantity.
- **`split_completeness_ceiling`**: De-chimerizing a bin $B$ into $B_1 \sqcup B_2$ can recover at most `Comp(B) + Cont(B)` in total completeness.
- **`stealth_chimera_exists`** *(Impossibility Theorem)*: For *every* marker family with $\ge 2$ distinct markers, two disjoint pure genomes merge into a **100%-complete, 0%-contaminated** chimeric MAG.
- **`accessory_invariance`**: Adding or removing arbitrary marker-free contigs (plasmids, prophages, accessory islands) leaves `Comp` and `Cont` strictly unchanged.

### 2. Finite-Sample Statistical Guarantees (`MAGLean/Probabilistic.lean`)
- **`hoeffding_lemma_bernoulli`**: First-principles calculus proof of `(1 - p)e^{-pt} + p e^{(1-p)t} ≤ e^{t^2/8}`.
- **`hoeffding_completeness_bound`**: Over $k$ independent collocated marker sets, $\Pr(|\widehat{p}_k - p| \ge \varepsilon) \le 2 e^{-2 k \varepsilon^2}$.
- **`marker_count_sufficient` & `hoeffdingRadius_strict_shrink`**: Certified sample-size formula $k \ge \frac{\ln(2/\delta)}{2\varepsilon^2}$ and proof that moving to a more specific clade with strictly more marker sets strictly shrinks the confidence radius.
- **`single_marker_chimeric_expectation` & `mimag_mq_evasion_expectation`**: Under independent target ($p$) and contaminant ($q$), $\mathbb{E}[\text{Comp}_{\text{obs}}] = p + q - pq$ and $\mathbb{E}[\text{Cont}_{\text{obs}}] = pq$—proving that a 50%-complete bin + 18% foreign genome yields 59% apparent completeness and 9% contamination (passing MIMAG MQ in expectation).

### 3. Taxonomic Hierarchy & GUNC-Style Purity (`MAGLean/Taxonomy.lean`)
- **`lineage_loss_bias_bound` & `lineage_loss_exact_complete`**: A reduced-genome clade (e.g. Patescibacteria / DPANN / symbionts) missing fraction $\lambda$ of ancestral markers has apparent ancestral completeness capped at $1 - \lambda$ even when 100% biologically complete.
- **`lca_zero_lineage_loss`**: Evaluating a MAG with phylogenetic placement uncertainty set $U$ at $\text{LCA}(U)$ guarantees zero lineage-loss bias across all $v \in U$.
- **`rank_refinement_monotonicity`**: Under tree-coherent contig taxonomy (`TaxCoherent`), conservative purity is monotonically non-increasing (and chimerism non-decreasing) from Domain to Species.
- **`purity_unclassified_sandwich`**: For *any* true assignment of unclassified contigs, true purity lies inside `[purityCons, purityOpt]`, with width equal to the unclassified bp fraction.
- **`unclassified_dilution_counterexample`**: Explicit tree-coherent chimeric bin whose drop-unclassified purity jumps artificially from `50%` (Phylum) to `100%` (Genus).
- **`taxonomic_catches_stealth_chimera`**: Merging two distinct clades $t_1 \ne t_2$ forces conservative purity $\frac{\max(W_1, W_2)}{W_1 + W_2} < 1$, closing the marker-only stealth-chimera loophole.

### 4. MIMAG Standards & Composite Scores (`MAGLean/Quality.lean`)
- **`mimag_partition_unique`**: Exact rational classification into four exhaustive, mutually exclusive tiers (`HQ`, `MQ`, `LQ`, `Contaminated`), explicitly closing the $\text{Cont} \ge 10\%$ gap in the prose 3-tier specification.
- **`mimag_hq_downgrade_missing_rna`**: Proves strict downgrade from HQ to MQ when rRNA/tRNA criteria fail.
- **`compositeScore_chimera_incentive` & `drep_Q5_chimera_threshold`**: Adding foreign fragment $c$ strictly *increases* $Q_\alpha = \text{Comp} - \alpha \cdot \text{Cont}$ iff $\text{Comp}(c) > (\alpha + 1)\cdot\text{Shared}(f, c) + \alpha\cdot\text{Cont}(c)$. For dRep/Parks $Q_5$ and pure contaminant $c$, $Q_5$ *rewards* contamination whenever $\text{Shared}(f, c) < \text{Comp}(c) / 6$.

### 5. ANI Dereplication (`MAGLean/Dereplication.lean`)
- **`ani_triangle_inequality_counterexample`**: Constructive 3-genome counterexample (`AF = 50%`, `ANI₁₂ = ANI₂₃ = 100%`, `ANI₁₃ = 0%`).
- **`ani_core_overlap_theorem`**: Whenever $\text{AF}_{12} + \text{AF}_{23} > 1$, the shared core has fraction $\ge \text{AF}_{12} + \text{AF}_{23} - 1$ and core identity:
  $$\text{ANI}_{13}^{\text{core}} \ge 1 - \frac{\text{AF}_{12}(1 - \text{ANI}_{12}) + \text{AF}_{23}(1 - \text{ANI}_{23})}{\text{AF}_{12} + \text{AF}_{23} - 1}$$
- **`derep_cluster_diameter_bound` & `derep_80_97_corollary`**: At `AF ≥ 80%` and `ANI ≥ 97%` to a representative, every intra-cluster pair shares `≥ 60%` core with `≥ 92%` core ANI.

### 6. Metagenome Binning & Verified Filtering (`MAGLean/Binning.lean`)
- **`global_metagenome_marker_conservation`**: Across *any* binning of assembly $A$ into bins $B_1, \dots, B_m$ plus unbinned contigs $U$, $\sum_b (\text{Comp}(B_b) + \text{Cont}(B_b)) + (\text{Comp}(U) + \text{Cont}(U)) = \text{Comp}(A) + \text{Cont}(A)$.
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
