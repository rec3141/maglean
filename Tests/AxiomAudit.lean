import MAGLean

/-!
# MAGLean Axiom Audit

Verifies that every flagship theorem in `MAGLean` depends exclusively on standard
Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) — zero `sorryAx`,
zero custom axioms, zero `Lean.ofReduceBool` / `native_decide` trust.
-/

-- 1. Marker Algebra, Conservation & Strain Heterogeneity (MAGLean.Markers)
#print axioms MAGLean.comp_add_cont_eq_mass
#print axioms MAGLean.conservation_law
#print axioms MAGLean.multi_conservation
#print axioms MAGLean.comp_add_eq
#print axioms MAGLean.cont_add_eq
#print axioms MAGLean.split_completeness_ceiling
#print axioms MAGLean.chimeric_masking_identity
#print axioms MAGLean.pure_merge_zero_cont_iff
#print axioms MAGLean.stealth_chimera_exists
#print axioms MAGLean.accessory_invariance
#print axioms MAGLean.nonStrainContamination_pair_weighting_discrepancy
#print axioms MAGLean.nonStrainContamination_exact_for_double_copies

-- 2. Finite-Sample Statistics & Concentration (MAGLean.Probabilistic)
#print axioms MAGLean.Probabilistic.empComp_expectation
#print axioms MAGLean.Probabilistic.empComp_variance
#print axioms MAGLean.Probabilistic.chebyshev_completeness_bound
#print axioms MAGLean.Probabilistic.hoeffding_lemma_bernoulli
#print axioms MAGLean.Probabilistic.hoeffding_lemma_bounded
#print axioms MAGLean.Probabilistic.hoeffding_completeness_bound
#print axioms MAGLean.Probabilistic.hoeffding_weighted_bounded
#print axioms MAGLean.Probabilistic.marker_count_sufficient
#print axioms MAGLean.Probabilistic.hoeffdingRadius_strict_shrink
#print axioms MAGLean.Probabilistic.single_marker_chimeric_expectation
#print axioms MAGLean.Probabilistic.chimeric_completeness_inflation
#print axioms MAGLean.Probabilistic.mimag_mq_evasion_expectation

-- 3. Taxonomic Hierarchy, Lineage Loss & Contig Purity (MAGLean.Taxonomy)
#print axioms MAGLean.Taxonomy.lineage_loss_bias_bound
#print axioms MAGLean.Taxonomy.lineage_loss_exact_complete
#print axioms MAGLean.Taxonomy.lca_zero_lineage_loss
#print axioms MAGLean.Taxonomy.purity_unclassified_sandwich
#print axioms MAGLean.Taxonomy.rank_refinement_monotonicity
#print axioms MAGLean.Taxonomy.rank_refinement_purityDrop_of_fully_classified
#print axioms MAGLean.Taxonomy.taxonomic_catches_stealth_chimera
#print axioms MAGLean.Taxonomy.unclassified_dilution_counterexample

-- 4. MIMAG Standards & Composite Quality Scores (MAGLean.Quality)
#print axioms MAGLean.Quality.mimag_partition_unique
#print axioms MAGLean.Quality.mimag_hq_downgrade_missing_rna
#print axioms MAGLean.Quality.compositeScore_pareto_mono
#print axioms MAGLean.Quality.compositeScore_chimera_incentive
#print axioms MAGLean.Quality.drep_Q5_chimera_threshold
#print axioms MAGLean.Quality.purityGatedScore_rejects_chimera

-- 5. ANI, Aligned Fraction & Dereplication (MAGLean.Dereplication)
#print axioms MAGLean.Dereplication.ani_core_overlap_theorem
#print axioms MAGLean.Dereplication.derep_cluster_diameter_bound
#print axioms MAGLean.Dereplication.derep_80_97_corollary
#print axioms MAGLean.Dereplication.ani_triangle_inequality_counterexample

-- 6. Binning Invariants & Global Conservation (MAGLean.Binning)
#print axioms MAGLean.Binning.binOf_disjoint
#print axioms MAGLean.Binning.assembly_length_conservation
#print axioms MAGLean.Binning.global_metagenome_marker_conservation
#print axioms MAGLean.Binning.filterValidBins_sound

-- 7. Executable Kernel Soundness Bridges (MAGLean.Certificate)
#print axioms MAGLean.Certificate.kCompleteness_eq_completeness
#print axioms MAGLean.Certificate.kContamination_eq_contamination
#print axioms MAGLean.Certificate.kMarkerMass_eq_markerMass
#print axioms MAGLean.Certificate.kCompositeQ5_eq_compositeScore
#print axioms MAGLean.Certificate.binMarkerCount_eq_binCounts
#print axioms MAGLean.Certificate.kCompleteness_add_kContamination_eq_kMarkerMass
#print axioms MAGLean.Certificate.kClassifyMIMAG_eq_classifyMIMAG
#print axioms MAGLean.Certificate.kStrainHeterogeneity_eq
#print axioms MAGLean.Certificate.kNonStrainCont_eq
#print axioms MAGLean.Certificate.kPurityGatedScore_eq_purityGatedScore
#print axioms MAGLean.Certificate.kCheckTaxCoherent_sound
#print axioms MAGLean.Certificate.kRankAudit_eq_taxonomy
#print axioms MAGLean.Certificate.kRankAudit_stealth_alert_sound
#print axioms MAGLean.Certificate.hoeffding95_cert_sound
#print axioms MAGLean.Certificate.kernel_hoeffding95_sound
