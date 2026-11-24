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

## Main Soundness Theorems

* `kPresent_eq_present`, `kExcess_eq_excess`: Exact identity of kernel vs. theory indicators.
* `kSetComp_add_kSetCont_eq_kSetMass`, `kCompleteness_add_kContamination_eq_kMarkerMass`:
  The executable kernel's completeness and contamination satisfy the exact rational
  conservation law `comp + cont = markerMass` on every input.
* `kClassifyMIMAG_eq_classifyMIMAG`: The executable kernel's MIMAG tier classifier
  matches the formally verified `Quality.classifyMIMAG` (and hence the exhaustive,
  mutually exclusive MIMAG partition theorem `Quality.mimag_partition_unique`) identically.
* `kStrainHeterogeneity_eq`, `kNonStrainCont_eq`: Exact agreement with `Markers`.
* `hoeffding95_cert_sound` & `kernel_hoeffding95_sound`: For every `k ≥ 2`, the rational
  radius `ε = Kernel.certifiedHoeffding95Radius k` emitted by the CLI provably certifies
  a ≥ 95% two-sided Hoeffding confidence interval `Pr(|empComp - p| ≥ ε) ≤ 1 / 20`.
* `checkTaxCoherent_sound`: Decidable soundness of the taxonomic tree-coherence checker,
  unlocking `Taxonomy.rank_refinement_monotonicity`.
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

/-! ### Exact Indicator & Marker Conservation Soundness of `MAGLean.Kernel` -/

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

/-- Per-set conservation law directly on the executable kernel functions. -/
theorem kSetComp_add_kSetCont_eq_kSetMass (s : List String) (f : String → ℕ) :
    kSetComp s f + kSetCont s f = kSetMass s f := by
  unfold kSetComp kSetCont kSetMass
  dsimp only
  split_ifs with hemp
  · simp
  · rw [← add_div]
    congr 1
    rw [foldl_add_nat, foldl_add_nat, foldl_add_nat]
    simp only [Nat.zero_add]
    have hpt :
        ((dedupStrings s).map (fun g => kPresent (f g))).sum +
          ((dedupStrings s).map (fun g => kExcess (f g))).sum =
        ((dedupStrings s).map f).sum := by
      rw [← list_sum_map_add_nat]
      congr 1
      apply List.map_congr_left
      intro g _
      rw [kPresent_eq_present, kExcess_eq_excess, present_add_excess]
    exact_mod_cast hpt

/-- **Kernel Marker-Mass Conservation Theorem**: For *every* marker family `sets` and
profile `f`, the executable CLI's `kCompleteness + kContamination = kMarkerMass` holds
identically in exact rational arithmetic. -/
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

/-! ### Verified Bridge from Rational CLI Radius to Real-Analysis Hoeffding Bounds -/

/-- **Rational-to-Real Hoeffding 95% Certificate Theorem**:
If a rational radius `ε > 0` satisfies `2 ≤ (k : ℚ) * ε ^ 2`, then under the
independent marker-set sampling model (`MAGLean.Probabilistic`),
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

/-- **End-to-End Soundness of the CLI's 95% Hoeffding Confidence Interval**:
For every marker family with `k ≥ 2` independent collocated sets, the exact rational
radius `ε = Kernel.certifiedHoeffding95Radius k` printed by `maglean` provably satisfies
`Pr(|empComp - p| ≥ ε) ≤ 0.05`. -/
theorem kernel_hoeffding95_sound {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let ε := Kernel.certifiedHoeffding95Radius k
    ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin k → Bool => (ε : ℝ) ≤ |Probabilistic.empComp ω - p|),
      Probabilistic.bernProb p ω ≤ (1 / 20 : ℝ) :=
  hoeffding95_cert_sound (by omega) hp0 hp1
    (certifiedHoeffding95Radius_pos k) (certifiedHoeffding95Radius_valid hk)

/-! ### Decidable Tree-Coherence Checker Soundness -/

/-- Decidable check for `Taxonomy.TaxCoherent` over a finite bin of contigs. -/
noncomputable def checkTaxCoherent {Contig Taxon : Type*} [DecidableEq Contig] [DecidableEq Taxon]
    (B : Finset Contig) (τ : Contig → TaxRank → Option Taxon) : Bool :=
  let ranks := TaxRank.all
  let cList := B.toList
  let prefixOk := cList.all fun c =>
    ranks.all fun r₁ =>
      ranks.all fun r₂ =>
        !(decide (r₁ ≤ r₂)) || !(τ c r₂).isSome || (τ c r₁).isSome
  let treeOk := cList.all fun c₁ =>
    cList.all fun c₂ =>
      ranks.all fun r₁ =>
        ranks.all fun r₂ =>
          !(decide (r₁ ≤ r₂)) ||
            match τ c₁ r₂, τ c₂ r₂ with
            | some t₁, some t₂ => !(decide (t₁ = t₂)) || decide (τ c₁ r₁ = τ c₂ r₁)
            | _, _ => true
  prefixOk && treeOk

private lemma mem_taxRank_all (r : TaxRank) : r ∈ TaxRank.all := by
  cases r <;> simp [TaxRank.all]

/-- **Soundness of the Decidable Tree-Coherence Checker**:
Whenever `checkTaxCoherent B τ = true`, the bin provably satisfies `Taxonomy.TaxCoherent B τ`,
unlocking `Taxonomy.rank_refinement_monotonicity` for the audited MAG. -/
theorem checkTaxCoherent_sound {Contig Taxon : Type*} [DecidableEq Contig] [DecidableEq Taxon]
    (B : Finset Contig) (τ : Contig → TaxRank → Option Taxon)
    (h : checkTaxCoherent B τ = true) :
    TaxCoherent B τ := by
  unfold checkTaxCoherent at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Finset.mem_toList] at h
  rcases h with ⟨hpref, htree⟩
  constructor
  · intro c hc r₁ r₂ hr hsome
    have h1 := hpref c hc r₁ (mem_taxRank_all r₁) r₂ (mem_taxRank_all r₂)
    rcases h1 with (hnle | hnsome) | hres
    · exact absurd hr hnle
    · rw [hsome] at hnsome; exact absurd hnsome (by decide)
    · exact hres
  · intro c₁ hc₁ c₂ hc₂ r₁ r₂ t hr h1 h2
    have h3 := htree c₁ hc₁ c₂ hc₂ r₁ (mem_taxRank_all r₁) r₂ (mem_taxRank_all r₂)
    rcases h3 with hnle | hmatch
    · exact absurd hr hnle
    · rw [h1, h2] at hmatch
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq, not_true_eq_false, false_or] at hmatch
      exact hmatch

end MAGLean.Certificate
