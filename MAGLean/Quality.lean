import MAGLean.Markers

/-!
# MAGLean.Quality

Formalization of the MIMAG (Minimum Information about a Metagenome-Assembled Genome,
Bowers et al. 2017) quality classification standard, composite ranking scores
`Q_α = Comp - α * Cont` (Parks et al. / dRep), and anti-chimerism score gating.

## Main Results

* `classifyMIMAG_iff_*`: Soundness and completeness of the computable MIMAG classifier
  with exact rational cutoffs (`9/10`, `1/20`, `1/2`, `1/10`).
* `mimag_partition_exhaustive`: Every MAG belongs to a unique tier in
  `{highQuality, mediumQuality, lowQuality, contaminated}`—exposing and closing the
  high-contamination gap in the original 3-tier prose specification.
* `mimag_hq_downgrade_missing_rna`: A MAG with `Comp > 90%` and `Cont < 5%` missing
  any rRNA subunit or having `< 18` distinct tRNAs downgrades strictly to `mediumQuality`.
* `compositeScore_pareto_mono`: `Q_α` respects Pareto dominance in `(Comp, -Cont)`.
* `compositeScore_chimera_incentive`: Exact necessary and sufficient condition under
  which adding a foreign fragment `c` strictly *increases* `Q_α`:
  `comp(c) > (α + 1) * shared(f, c) + α * cont(c)`.
* `drep_Q5_chimera_threshold`: Corollary for `α = 5` (dRep/Parks)—any pure contaminant
  whose markers overlap `< 1/6` of its own completeness is *rewarded* by `Q_5`.
-/

namespace MAGLean.Quality

/-- Ribosomal & transfer RNA completeness profile required by MIMAG High Quality. -/
structure RNAProfile where
  has23S : Bool
  has16S : Bool
  has5S : Bool
  distinctTRNAs : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace RNAProfile

/-- MIMAG High-Quality RNA requirement: 23S, 16S, and 5S rRNA genes plus at least
18 distinct tRNA types. -/
def satisfiesHQ (r : RNAProfile) : Bool :=
  r.has23S && r.has16S && r.has5S && decide (18 ≤ r.distinctTRNAs)

theorem satisfiesHQ_iff (r : RNAProfile) :
    r.satisfiesHQ = true ↔
      r.has23S = true ∧ r.has16S = true ∧ r.has5S = true ∧ 18 ≤ r.distinctTRNAs := by
  unfold satisfiesHQ
  simp [Bool.and_eq_true, and_assoc]

end RNAProfile

/-- Exhaustive MIMAG quality tiers, including the explicit `contaminated` tier
(`contamination ≥ 10%`) left implicit by the original 3-tier HQ/MQ/LQ table. -/
inductive MIMAGTier where
  | highQuality
  | mediumQuality
  | lowQuality
  | contaminated
  deriving DecidableEq, Repr, Inhabited

namespace MIMAGTier

def label : MIMAGTier → String
  | highQuality   => "High-Quality (MIMAG HQ)"
  | mediumQuality => "Medium-Quality (MIMAG MQ)"
  | lowQuality    => "Low-Quality (MIMAG LQ)"
  | contaminated  => "Contaminated (Failed MIMAG <10% Cont)"

end MIMAGTier

/-! ### Semantic MIMAG Specifications (Exact Rationals) -/

/-- MIMAG High-Quality draft specification (Bowers et al., 2017):
`comp > 90%`, `cont < 5%`, and full rRNA (23S, 16S, 5S) + `≥ 18` distinct tRNAs. -/
def IsMIMAG_HQ (comp cont : ℚ) (rna : RNAProfile) : Prop :=
  (9 / 10 : ℚ) < comp ∧ cont < (1 / 20 : ℚ) ∧ rna.satisfiesHQ = true

/-- MIMAG Medium-Quality draft specification:
`comp ≥ 50%`, `cont < 10%`, and not already High-Quality. -/
def IsMIMAG_MQ (comp cont : ℚ) (rna : RNAProfile) : Prop :=
  (1 / 2 : ℚ) ≤ comp ∧ cont < (1 / 10 : ℚ) ∧ ¬ IsMIMAG_HQ comp cont rna

/-- MIMAG Low-Quality draft specification:
`comp < 50%` and `cont < 10%`. -/
def IsMIMAG_LQ (comp cont : ℚ) : Prop :=
  comp < (1 / 2 : ℚ) ∧ cont < (1 / 10 : ℚ)

/-- High-contamination tier: `cont ≥ 10%` (fails MIMAG LQ/MQ/HQ). -/
def IsMIMAG_Contaminated (cont : ℚ) : Prop :=
  (1 / 10 : ℚ) ≤ cont

/-- Computable, exact rational MIMAG tier classifier. -/
def classifyMIMAG (comp cont : ℚ) (rna : RNAProfile) : MIMAGTier :=
  if (9 / 10 : ℚ) < comp ∧ cont < (1 / 20 : ℚ) ∧ rna.satisfiesHQ = true then
    .highQuality
  else if (1 / 2 : ℚ) ≤ comp ∧ cont < (1 / 10 : ℚ) then
    .mediumQuality
  else if cont < (1 / 10 : ℚ) then
    .lowQuality
  else
    .contaminated

theorem classifyMIMAG_eq_hq_iff (comp cont : ℚ) (rna : RNAProfile) :
    classifyMIMAG comp cont rna = .highQuality ↔ IsMIMAG_HQ comp cont rna := by
  unfold classifyMIMAG IsMIMAG_HQ
  split_ifs <;> simp_all

theorem classifyMIMAG_eq_mq_iff (comp cont : ℚ) (rna : RNAProfile) :
    classifyMIMAG comp cont rna = .mediumQuality ↔ IsMIMAG_MQ comp cont rna := by
  unfold classifyMIMAG IsMIMAG_MQ IsMIMAG_HQ
  split_ifs with h1 h2 h3
  · simp only [false_iff]; intro ⟨_, _, hnot⟩; exact hnot h1
  · simp only [true_iff]; exact ⟨h2.1, h2.2, h1⟩
  · simp only [false_iff]; intro ⟨hge, hlt, _⟩; exact h2 ⟨hge, hlt⟩
  · simp only [false_iff]; intro ⟨_, hlt, _⟩; exact h3 hlt

theorem classifyMIMAG_eq_lq_iff (comp cont : ℚ) (rna : RNAProfile) :
    classifyMIMAG comp cont rna = .lowQuality ↔ IsMIMAG_LQ comp cont := by
  unfold classifyMIMAG IsMIMAG_LQ
  split_ifs with h1 h2 h3
  · simp; intro hlt; exfalso; linarith [h1.1]
  · simp; intro hlt; exfalso; linarith [h2.1]
  · simp only [true_iff]
    refine ⟨?_, h3⟩
    by_contra hge
    push Not at hge
    exact h2 ⟨hge, h3⟩
  · simp; intro _; linarith

theorem classifyMIMAG_eq_cont_iff (comp cont : ℚ) (rna : RNAProfile) :
    classifyMIMAG comp cont rna = .contaminated ↔ IsMIMAG_Contaminated cont := by
  unfold classifyMIMAG IsMIMAG_Contaminated
  split_ifs with h1 h2 h3
  · simp; linarith [h1.2.1]
  · simp; linarith [h2.2]
  · simp; linarith [h3]
  · simp; linarith

/-- **MIMAG Exhaustive & Mutually Exclusive Partition Theorem**:
Every `(comp, cont, rna)` satisfies *exactly one* of `HQ`, `MQ`, `LQ`, or `Contaminated`. -/
theorem mimag_partition_unique (comp cont : ℚ) (rna : RNAProfile) :
    (IsMIMAG_HQ comp cont rna ∨ IsMIMAG_MQ comp cont rna ∨
      IsMIMAG_LQ comp cont ∨ IsMIMAG_Contaminated cont) ∧
    (IsMIMAG_HQ comp cont rna → ¬ IsMIMAG_MQ comp cont rna) ∧
    (IsMIMAG_HQ comp cont rna → ¬ IsMIMAG_LQ comp cont) ∧
    (IsMIMAG_HQ comp cont rna → ¬ IsMIMAG_Contaminated cont) ∧
    (IsMIMAG_MQ comp cont rna → ¬ IsMIMAG_LQ comp cont) ∧
    (IsMIMAG_MQ comp cont rna → ¬ IsMIMAG_Contaminated cont) ∧
    (IsMIMAG_LQ comp cont → ¬ IsMIMAG_Contaminated cont) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases h : classifyMIMAG comp cont rna with
    | highQuality   => left; exact (classifyMIMAG_eq_hq_iff comp cont rna).mp h
    | mediumQuality => right; left; exact (classifyMIMAG_eq_mq_iff comp cont rna).mp h
    | lowQuality    => right; right; left; exact (classifyMIMAG_eq_lq_iff comp cont rna).mp h
    | contaminated  => right; right; right; exact (classifyMIMAG_eq_cont_iff comp cont rna).mp h
  · intro h1 h2; exact h2.2.2 h1
  · intro h1 h2; unfold IsMIMAG_HQ IsMIMAG_LQ at *; linarith [h1.1, h2.1]
  · intro h1 h2; unfold IsMIMAG_HQ IsMIMAG_Contaminated at *; linarith [h1.2.1, h2]
  · intro h1 h2; unfold IsMIMAG_MQ IsMIMAG_LQ at *; linarith [h1.1, h2.1]
  · intro h1 h2; unfold IsMIMAG_MQ IsMIMAG_Contaminated at *; linarith [h1.2.1, h2]
  · intro h1 h2; unfold IsMIMAG_LQ IsMIMAG_Contaminated at *; linarith [h1.2, h2]

/-- **HQ-to-MQ RNA Downgrade Theorem**: A bin exceeding the HQ marker thresholds
(`comp > 90%`, `cont < 5%`) that lacks required rRNA/tRNA annotations is classified
strictly as `mediumQuality`, never `highQuality` or `lowQuality`. -/
theorem mimag_hq_downgrade_missing_rna {comp cont : ℚ} {rna : RNAProfile}
    (hcomp : (9 / 10 : ℚ) < comp) (hcont : cont < (1 / 20 : ℚ))
    (hrna : rna.satisfiesHQ = false) :
    classifyMIMAG comp cont rna = .mediumQuality := by
  rw [classifyMIMAG_eq_mq_iff]
  refine ⟨by linarith, by linarith, ?_⟩
  intro hq
  unfold IsMIMAG_HQ at hq
  rw [hrna] at hq
  exact Bool.false_ne_true hq.2.2

/-! ### Composite Quality Score `Q_α = Comp - α * Cont` & Chimera Incentives -/

section CompositeScore

variable {α_m : Type*} [DecidableEq α_m]

/-- Linear composite quality score `Q_α(f) = completeness - α * contamination`
(e.g., Parks et al. / dRep use `α = 5`). -/
def compositeScore (pen : ℚ) (M : MarkerFamily α_m) (f : α_m → ℕ) : ℚ :=
  completeness M f - pen * contamination M f

/-- **Pareto Monotonicity**: For `pen ≥ 0`, higher completeness and lower contamination
never decrease `compositeScore`. -/
theorem compositeScore_pareto_mono {pen : ℚ} (hpen : 0 ≤ pen) (M : MarkerFamily α_m)
    {f₁ f₂ : α_m → ℕ}
    (hcomp : completeness M f₁ ≤ completeness M f₂)
    (hcont : contamination M f₂ ≤ contamination M f₁) :
    compositeScore pen M f₁ ≤ compositeScore pen M f₂ := by
  unfold compositeScore
  nlinarith

/-- **Exact Delta Identity for Composite Score**: Adding fragment `c` to bin `f` changes
`Q_α` by *exactly* `comp(c) - (α + 1) * shared(f, c) - α * cont(c)`. -/
theorem compositeScore_add_delta (pen : ℚ) (M : MarkerFamily α_m) (f c : α_m → ℕ) :
    compositeScore pen M (f + c) - compositeScore pen M f =
      completeness M c - (pen + 1) * sharedCompleteness M f c - pen * contamination M c := by
  unfold compositeScore
  have hcomp := comp_add_eq M f c
  have hcont := cont_add_eq M f c
  linear_combination hcomp - pen * hcont

/-- **Chimera-Incentive Theorem**: Greedy optimization of `Q_α = Comp - α * Cont`
strictly *rewards* merging a foreign fragment `c` into `f` if and only if
`comp(c) > (α + 1) * shared(f, c) + α * cont(c)`. -/
theorem compositeScore_chimera_incentive (pen : ℚ) (M : MarkerFamily α_m) (f c : α_m → ℕ) :
    compositeScore pen M f < compositeScore pen M (f + c) ↔
      (pen + 1) * sharedCompleteness M f c + pen * contamination M c < completeness M c := by
  have h := compositeScore_add_delta pen M f c
  constructor <;> intro hlt <;> linarith

/-- **dRep / Parks `Q_5` Chimera Threshold Corollary**: For `α = 5` and a pure foreign
fragment `c` (`cont(c) = 0`), adding `c` strictly *increases* `Q_5` whenever
`shared(f, c) < comp(c) / 6`! -/
theorem drep_Q5_chimera_threshold (M : MarkerFamily α_m) (f c : α_m → ℕ)
    (hpure : contamination M c = 0) :
    compositeScore 5 M f < compositeScore 5 M (f + c) ↔
      sharedCompleteness M f c < completeness M c / 6 := by
  rw [compositeScore_chimera_incentive, hpure]
  constructor <;> intro h <;> linarith

/-- **Purity-Gated Quality Score**: Returns `some (Q_α)` only if contig-level taxonomic
purity meets threshold `τ_p`, blocking chimeric score inflation. -/
def purityGatedScore (pen τ_p : ℚ) (comp cont purity : ℚ) : Option ℚ :=
  if τ_p ≤ purity then some (comp - pen * cont) else none

theorem purityGatedScore_rejects_chimera {pen τ_p comp cont purity : ℚ}
    (hchim : purity < τ_p) :
    purityGatedScore pen τ_p comp cont purity = none := by
  unfold purityGatedScore
  exact ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hchim))

end CompositeScore

end MAGLean.Quality
