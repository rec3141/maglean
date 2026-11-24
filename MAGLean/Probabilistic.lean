import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# MAGLean.Probabilistic

Finite-sample statistical guarantees and expectation theorems for marker-based MAG
completeness and contamination estimation.

## Main Results

* `hoeffding_lemma_bernoulli`: Exact proof from first principles that for every
  `p ∈ [0, 1]` and `t : ℝ`, `(1 - p) * exp (-p * t) + p * exp ((1 - p) * t) ≤ exp (t ^ 2 / 8)`.
* `empComp_expectation`: Unbiasedness of empirical completeness over `k` independent
  marker sets (`𝔼[empComp] = p`).
* `empComp_variance_le`: Exact variance `p * (1 - p) / k ≤ 1 / (4 * k)`.
* `chebyshev_completeness_bound`: Finite-sample Chebyshev bound `Pr(|empComp - p| ≥ ε) ≤ 1 / (4 * k * ε ^ 2)`.
* `hoeffding_completeness_bound`: Two-sided exponential Hoeffding bound
  `Pr(|empComp - p| ≥ ε) ≤ 2 * exp (-2 * k * ε ^ 2)`.
* `marker_count_sufficient`: Certified sample-size formula—if `k ≥ log (2 / δ) / (2 * ε ^ 2)`,
  then `Pr(|empComp - p| ≥ ε) ≤ δ`.
* `chimeric_expectation_comp`, `chimeric_expectation_cont`: Under independent target
  completeness `p` and contaminant completeness `q`, `𝔼[Comp_obs] = p + q - p * q` and
  `𝔼[Cont_obs] = p * q`, proving artificial completeness inflation `q * (1 - p)` and
  contamination hiding fraction `(1 - p)`.
* `mimag_mq_evasion_expectation`: Explicit witness (`p = 0.5, q = 0.18`) showing an 18%
  foreign-genome chimera passes MIMAG Medium Quality in expectation (`0.59 ≥ 0.50`, `0.09 < 0.10`).
-/

namespace MAGLean.Probabilistic

noncomputable section

open scoped BigOperators
open Finset Real

/-! ### Discrete Product Bernoulli Space on `Fin k → Bool` -/

/-- Single-trial Bernoulli probability weight. -/
def bernWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Product Bernoulli probability of a presence/absence vector `ω : Fin k → Bool`. -/
def bernProb {k : ℕ} (p : ℝ) (ω : Fin k → Bool) : ℝ :=
  ∏ i : Fin k, bernWeight p (ω i)

/-- Indicator `0`/`1` of a single marker hit. -/
def indBool (b : Bool) : ℝ := if b then 1 else 0

/-- Empirical completeness across `k` independent marker sets. -/
def empComp {k : ℕ} (ω : Fin k → Bool) : ℝ :=
  (∑ i : Fin k, indBool (ω i)) / (k : ℝ)

lemma bernWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bernWeight p b := by
  cases b <;> simp [bernWeight] <;> linarith

lemma bernProb_nonneg {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : Fin k → Bool) :
    0 ≤ bernProb p ω := by
  unfold bernProb
  exact Finset.prod_nonneg (fun i _ => bernWeight_nonneg hp0 hp1 (ω i))

lemma sum_bernWeight (p : ℝ) : ∑ b : Bool, bernWeight p b = 1 := by
  simp [bernWeight]

/-- Total probability of the product Bernoulli model equals `1`. -/
theorem sum_bernProb (k : ℕ) (p : ℝ) :
    ∑ ω : Fin k → Bool, bernProb p ω = 1 := by
  unfold bernProb
  rw [← Fintype.prod_sum (fun (_ : Fin k) (b : Bool) => bernWeight p b)]
  simp [bernWeight]

/-- Factorization of product expectations over `Fin k → Bool`. -/
lemma sum_bernProb_prod {k : ℕ} (p : ℝ) (g : Fin k → Bool → ℝ) :
    ∑ ω : Fin k → Bool, bernProb p ω * (∏ i : Fin k, g i (ω i)) =
      ∏ i : Fin k, ∑ b : Bool, bernWeight p b * g i b := by
  have h1 : ∀ ω : Fin k → Bool,
      bernProb p ω * (∏ i : Fin k, g i (ω i)) =
        ∏ i : Fin k, (bernWeight p (ω i) * g i (ω i)) := by
    intro ω
    unfold bernProb
    rw [← Finset.prod_mul_distrib]
  simp_rw [h1]
  exact (Fintype.prod_sum (fun i b => bernWeight p b * g i b)).symm

/-- Expectation of a single coordinate indicator `indBool (ω j)` equals `p`. -/
lemma exp_single_ind {k : ℕ} (p : ℝ) (j : Fin k) :
    ∑ ω : Fin k → Bool, bernProb p ω * indBool (ω j) = p := by
  have hprod : ∀ ω : Fin k → Bool,
      indBool (ω j) = ∏ i : Fin k, (if i = j then indBool (ω i) else 1) := by
    intro ω
    rw [Finset.prod_ite_eq']
    simp
  simp_rw [hprod]
  rw [sum_bernProb_prod p (fun i b => if i = j then indBool b else 1)]
  have hterm : ∀ i : Fin k,
      (∑ b : Bool, bernWeight p b * (if i = j then indBool b else 1)) =
        if i = j then p else 1 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [bernWeight, indBool]
    · simp [hij, bernWeight]
  simp_rw [hterm]
  rw [Finset.prod_ite_eq']
  simp

/-- Expectation of a product of two distinct coordinate indicators equals `p ^ 2`. -/
lemma exp_pair_ind {k : ℕ} (p : ℝ) {i j : Fin k} (hij : i ≠ j) :
    ∑ ω : Fin k → Bool, bernProb p ω * (indBool (ω i) * indBool (ω j)) = p * p := by
  have hprod : ∀ ω : Fin k → Bool,
      indBool (ω i) * indBool (ω j) =
        ∏ m : Fin k, (if m = i then indBool (ω m) else if m = j then indBool (ω m) else 1) := by
    intro ω
    have hsplit :
        ∏ m : Fin k, (if m = i then indBool (ω m) else if m = j then indBool (ω m) else 1) =
          (if i = i then indBool (ω i) else if i = j then indBool (ω i) else 1) *
          ∏ m ∈ Finset.univ.erase i,
            (if m = i then indBool (ω m) else if m = j then indBool (ω m) else 1) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    rw [hsplit]
    simp only [↓reduceIte]
    have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ hjmem]
    have hji : j ≠ i := Ne.symm hij
    simp only [hji, ↓reduceIte]
    have hrest :
        ∏ m ∈ (Finset.univ.erase i).erase j,
          (if m = i then indBool (ω m) else if m = j then indBool (ω m) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro m hm
      have hm1 : m ≠ j := (Finset.mem_erase.mp hm).1
      have hm2 : m ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      simp [hm1, hm2]
    rw [hrest, mul_one]
  simp_rw [hprod]
  rw [sum_bernProb_prod p (fun m b => if m = i then indBool b else if m = j then indBool b else 1)]
  have hterm : ∀ m : Fin k,
      (∑ b : Bool, bernWeight p b *
        (if m = i then indBool b else if m = j then indBool b else 1)) =
        if m = i then p else if m = j then p else 1 := by
    intro m
    by_cases hmi : m = i
    · subst hmi; simp [bernWeight, indBool]
    · by_cases hmj : m = j
      · subst hmj; simp [hmi, bernWeight, indBool]
      · simp [hmi, hmj, bernWeight]
  simp_rw [hterm]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [↓reduceIte]
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ hjmem]
  have hji : j ≠ i := Ne.symm hij
  simp only [hji, ↓reduceIte]
  have hrest :
      ∏ m ∈ (Finset.univ.erase i).erase j,
        (if m = i then p else if m = j then p else 1) = 1 := by
    apply Finset.prod_eq_one
    intro m hm
    have hm1 : m ≠ j := (Finset.mem_erase.mp hm).1
    have hm2 : m ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
    simp [hm1, hm2]
  rw [hrest, mul_one]

/-- **Unbiasedness of Empirical Completeness**: `𝔼[empComp] = p`. -/
theorem empComp_expectation {k : ℕ} (hk : 0 < k) (p : ℝ) :
    ∑ ω : Fin k → Bool, bernProb p ω * empComp ω = p := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  unfold empComp
  have h1 : ∀ ω : Fin k → Bool,
      bernProb p ω * ((∑ i : Fin k, indBool (ω i)) / (k : ℝ)) =
        (∑ i : Fin k, bernProb p ω * indBool (ω i)) / (k : ℝ) := by
    intro ω
    rw [mul_div_assoc', Finset.mul_sum]
  simp_rw [h1]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [exp_single_ind]
  simp [hkne]

/-- **Exact Variance of Empirical Completeness**: `Var(empComp) = p * (1 - p) / k`. -/
theorem empComp_variance {k : ℕ} (hk : 0 < k) (p : ℝ) :
    ∑ ω : Fin k → Bool, bernProb p ω * (empComp ω - p) ^ 2 = p * (1 - p) / (k : ℝ) := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hexpand : ∀ ω : Fin k → Bool,
      bernProb p ω * (empComp ω - p) ^ 2 =
        bernProb p ω * (empComp ω) ^ 2 - 2 * p * (bernProb p ω * empComp ω) +
          p ^ 2 * bernProb p ω := by
    intro ω; ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [empComp_expectation hk p, sum_bernProb]
  -- Now compute `∑ ω, bernProb p ω * (empComp ω) ^ 2`
  have hsq : ∑ ω : Fin k → Bool, bernProb p ω * (empComp ω) ^ 2 =
      (p + ((k : ℝ) - 1) * p * p) / (k : ℝ) := by
    unfold empComp
    have hstep : ∀ ω : Fin k → Bool,
        bernProb p ω * ((∑ i : Fin k, indBool (ω i)) / (k : ℝ)) ^ 2 =
          (∑ i : Fin k, ∑ j : Fin k, bernProb p ω * (indBool (ω i) * indBool (ω j))) /
            ((k : ℝ) ^ 2) := by
      intro ω
      rw [div_pow, mul_div_assoc', sq, Finset.sum_mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    simp_rw [hstep]
    rw [← Finset.sum_div, Finset.sum_comm]
    have hinner :
        ∑ i : Fin k, ∑ ω : Fin k → Bool, ∑ j : Fin k,
          bernProb p ω * (indBool (ω i) * indBool (ω j)) =
          (k : ℝ) * (p + ((k : ℝ) - 1) * p * p) := by
      have hswap : ∀ i : Fin k,
          ∑ ω : Fin k → Bool, ∑ j : Fin k,
            bernProb p ω * (indBool (ω i) * indBool (ω j)) =
            p + ((k : ℝ) - 1) * p * p := by
        intro i
        rw [Finset.sum_comm]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        have hdiag : ∑ ω : Fin k → Bool, bernProb p ω * (indBool (ω i) * indBool (ω i)) = p := by
          have hid : ∀ ω : Fin k → Bool, indBool (ω i) * indBool (ω i) = indBool (ω i) := by
            intro ω; cases ω i <;> simp [indBool]
          simp_rw [hid]
          exact exp_single_ind p i
        have hoff : ∑ j ∈ Finset.univ.erase i,
            ∑ ω : Fin k → Bool, bernProb p ω * (indBool (ω i) * indBool (ω j)) =
              ((k : ℝ) - 1) * (p * p) := by
          have hterm : ∀ j ∈ Finset.univ.erase i,
              ∑ ω : Fin k → Bool, bernProb p ω * (indBool (ω i) * indBool (ω j)) = p * p := by
            intro j hj
            exact exp_pair_ind p (Ne.symm (Finset.mem_erase.mp hj).1)
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub hk, Nat.cast_one]
          rw [hcast]
        rw [hdiag, hoff]
        ring
      simp_rw [hswap]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hinner]
    field_simp [hkne]
  rw [hsq]
  field_simp [hkne]
  ring

/-- Universal variance ceiling `p * (1 - p) / k ≤ 1 / (4 * k)`. -/
theorem empComp_variance_le {k : ℕ} (hk : 0 < k) (p : ℝ) :
    ∑ ω : Fin k → Bool, bernProb p ω * (empComp ω - p) ^ 2 ≤ 1 / (4 * (k : ℝ)) := by
  rw [empComp_variance hk p]
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hquad : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  calc p * (1 - p) / (k : ℝ)
      ≤ (1 / 4) / (k : ℝ) := div_le_div_of_nonneg_right hquad (le_of_lt hkpos)
    _ = 1 / (4 * (k : ℝ)) := by ring

/-- **Finite-Sample Chebyshev Bound** for marker-based completeness estimation. -/
theorem chebyshev_completeness_bound {k : ℕ} (hk : 0 < k) {p ε : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
        bernProb p ω ≤ 1 / (4 * (k : ℝ) * ε ^ 2) := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmarkov :
      ε ^ 2 * ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
          bernProb p ω ≤
        ∑ ω : Fin k → Bool, bernProb p ω * (empComp ω - p) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
            ε ^ 2 * bernProb p ω
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
            bernProb p ω * (empComp ω - p) ^ 2 := by
          apply Finset.sum_le_sum
          intro ω hω
          have habs : ε ≤ |empComp ω - p| := (Finset.mem_filter.mp hω).2
          have hsq : ε ^ 2 ≤ (empComp ω - p) ^ 2 := by
            rw [← sq_abs (empComp ω - p)]
            nlinarith [abs_nonneg (empComp ω - p)]
          have hprob : 0 ≤ bernProb p ω := bernProb_nonneg hp0 hp1 ω
          nlinarith
      _ ≤ ∑ ω : Fin k → Bool, bernProb p ω * (empComp ω - p) ^ 2 := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro ω
          exact mul_nonneg (bernProb_nonneg hp0 hp1 ω) (sq_nonneg _)
  have hvar := empComp_variance_le hk p
  have hcomb :
      ε ^ 2 * ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
          bernProb p ω ≤ 1 / (4 * (k : ℝ)) := le_trans hmarkov hvar
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ) * ε ^ 2)]
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))).mp hcomb
  nlinarith

/-! ### Hoeffding's Lemma & Exponential Concentration Bound -/

/-- **Hoeffding's Lemma for a Bernoulli Random Variable** (proved from first principles
via second-derivative concavity of the cumulant generating function). -/
theorem hoeffding_lemma_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (1 - p) * Real.exp (-p * t) + p * Real.exp ((1 - p) * t) ≤ Real.exp (t ^ 2 / 8) := by
  by_cases hpz : p = 0
  · subst hpz
    simp only [sub_zero, neg_zero, zero_mul, Real.exp_zero, mul_one, one_mul, add_zero]
    exact Real.one_le_exp (by positivity)
  by_cases hpo : p = 1
  · subst hpo
    simp only [sub_self, zero_mul, Real.exp_zero, mul_one, zero_add]
    exact Real.one_le_exp (by positivity)
  have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have h1p_pos : 0 < 1 - p := by linarith [lt_of_le_of_ne hp1 hpo]
  -- Define `f(x) = 1 - p + p * exp x > 0` and `h(x) = log(f(x)) - p * x - x^2 / 8`
  let f : ℝ → ℝ := fun x => 1 - p + p * Real.exp x
  let h : ℝ → ℝ := fun x => Real.log (f x) - p * x - x ^ 2 / 8
  let h' : ℝ → ℝ := fun x => (p * Real.exp x) / f x - p - x / 4
  have hf_pos : ∀ x, 0 < f x := fun x => by
    dsimp [f]
    positivity
  have hf_ne : ∀ x, f x ≠ 0 := fun x => ne_of_gt (hf_pos x)
  have h_hasDeriv : ∀ x, HasDerivAt h (h' x) x := by
    intro x
    have hdf : HasDerivAt f (p * Real.exp x) x := by
      have h1 : HasDerivAt (fun y => p * Real.exp y) (p * Real.exp x) x :=
        (Real.hasDerivAt_exp x).const_mul p
      simpa [f] using h1.const_add (1 - p)
    have hlog : HasDerivAt (fun y => Real.log (f y)) ((p * Real.exp x) / f x) x :=
      hdf.log (hf_ne x)
    have hlin : HasDerivAt (fun y => p * y) p x := by
      simpa using (hasDerivAt_id x).const_mul p
    have hquad : HasDerivAt (fun y => y ^ 2 / 8) (x / 4) x := by
      have h2 := (hasDerivAt_pow 2 x).div_const (8 : ℝ)
      convert h2 using 1
      ring
    exact (hlog.sub hlin).sub hquad
  have h'_hasDeriv : ∀ x,
      HasDerivAt h' (((1 - p) * p * Real.exp x) / (f x) ^ 2 - 1 / 4) x := by
    intro x
    have hdf : HasDerivAt f (p * Real.exp x) x := by
      have h1 : HasDerivAt (fun y => p * Real.exp y) (p * Real.exp x) x :=
        (Real.hasDerivAt_exp x).const_mul p
      simpa [f] using h1.const_add (1 - p)
    have hnum : HasDerivAt (fun y => p * Real.exp y) (p * Real.exp x) x :=
      (Real.hasDerivAt_exp x).const_mul p
    have hdiv := hnum.div hdf (hf_ne x)
    have hdiv' : HasDerivAt (fun y => (p * Real.exp y) / f y)
        (((1 - p) * p * Real.exp x) / (f x) ^ 2) x := by
      convert hdiv using 1
      dsimp [f]
      ring
    have hconst : HasDerivAt (fun _ : ℝ => p) 0 x := hasDerivAt_const x p
    have hlin : HasDerivAt (fun y => y / 4) (1 / 4) x := by
      simpa using (hasDerivAt_id x).div_const (4 : ℝ)
    have hsub := (hdiv'.sub hconst).sub hlin
    convert hsub using 1
    ring
  have h'_deriv_nonpos : ∀ x, deriv h' x ≤ 0 := by
    intro x
    rw [(h'_hasDeriv x).deriv]
    have hfx_pos : 0 < f x := hf_pos x
    have hfx2_pos : 0 < (f x) ^ 2 := sq_pos_of_pos hfx_pos
    rw [sub_nonpos, div_le_iff₀ hfx2_pos]
    -- `4 * (1 - p) * p * exp x ≤ (1 - p + p * exp x)^2` since `(1 - p - p * exp x)^2 ≥ 0`
    dsimp [f]
    nlinarith [sq_nonneg ((1 - p) - p * Real.exp x)]
  have h'_anti : Antitone h' :=
    antitone_of_deriv_nonpos (fun x => (h'_hasDeriv x).differentiableAt) h'_deriv_nonpos
  have h'0 : h' 0 = 0 := by
    dsimp [h', f]
    simp
  have h0 : h 0 = 0 := by
    dsimp [h, f]
    simp
  have h_cont : Continuous h :=
    continuous_iff_continuousAt.mpr (fun x => (h_hasDeriv x).differentiableAt.continuousAt)
  have ht_le_zero : h t ≤ 0 := by
    rcases le_total 0 t with ht | ht
    · -- On `[0, ∞)`, `h' ≤ 0`, so `h` is antitone on `Set.Ici 0`
      have hanti_pos : AntitoneOn h (Set.Ici 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
        · exact h_cont.continuousOn
        · exact fun x _ => (h_hasDeriv x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [(h_hasDeriv x).deriv]
          have hx0 : 0 ≤ x := le_of_lt (by simpa [interior_Ici] using hx)
          calc h' x ≤ h' 0 := h'_anti hx0
            _ = 0 := h'0
      calc h t ≤ h 0 := hanti_pos (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr ht) ht
        _ = 0 := h0
    · -- On `(-∞, 0]`, `h' ≥ 0`, so `h` is monotone on `Set.Iic 0`
      have hmono_neg : MonotoneOn h (Set.Iic 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
        · exact h_cont.continuousOn
        · exact fun x _ => (h_hasDeriv x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [(h_hasDeriv x).deriv]
          have hx0 : x ≤ 0 := le_of_lt (by simpa [interior_Iic] using hx)
          calc (0 : ℝ) = h' 0 := h'0.symm
            _ ≤ h' x := h'_anti hx0
      calc h t ≤ h 0 := hmono_neg (Set.mem_Iic.mpr ht) (Set.mem_Iic.mpr (le_refl 0)) ht
        _ = 0 := h0
  -- Convert `log(f t) ≤ p * t + t^2 / 8` to the exponential inequality
  have hlog_le : Real.log (f t) ≤ p * t + t ^ 2 / 8 := by
    dsimp [h] at ht_le_zero
    linarith
  have hexp_le : f t ≤ Real.exp (p * t + t ^ 2 / 8) := by
    calc f t = Real.exp (Real.log (f t)) := (Real.exp_log (hf_pos t)).symm
      _ ≤ Real.exp (p * t + t ^ 2 / 8) := Real.exp_le_exp.mpr hlog_le
  have hmul := mul_le_mul_of_nonneg_left hexp_le (le_of_lt (Real.exp_pos (-p * t)))
  have hlhs : Real.exp (-p * t) * f t =
      (1 - p) * Real.exp (-p * t) + p * Real.exp ((1 - p) * t) := by
    dsimp [f]
    rw [mul_add]
    have h2 : Real.exp (-p * t) * (p * Real.exp t) = p * Real.exp ((1 - p) * t) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [h2, mul_comm (Real.exp (-p * t)) (1 - p)]
  have hrhs : Real.exp (-p * t) * Real.exp (p * t + t ^ 2 / 8) = Real.exp (t ^ 2 / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linarith

/-- Moment generating function bound for the centered sum `∑ (X_i - p)`. -/
theorem mgf_bound_bernoulli_sum {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    ∑ ω : Fin k → Bool,
        bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) ≤
      Real.exp ((k : ℝ) * t ^ 2 / 8) := by
  have hprod : ∀ ω : Fin k → Bool,
      Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) =
        ∏ i : Fin k, Real.exp (t * (indBool (ω i) - p)) := by
    intro ω
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hprod]
  rw [sum_bernProb_prod p (fun _ b => Real.exp (t * (indBool b - p)))]
  have hsingle : ∀ i : Fin k,
      (∑ b : Bool, bernWeight p b * Real.exp (t * (indBool b - p))) ≤
        Real.exp (t ^ 2 / 8) := by
    intro i
    have hrew : (∑ b : Bool, bernWeight p b * Real.exp (t * (indBool b - p))) =
        (1 - p) * Real.exp (-p * t) + p * Real.exp ((1 - p) * t) := by
      simp only [Fintype.sum_bool, bernWeight, indBool, ↓reduceIte, Bool.false_eq_true]
      have h1 : t * (1 - p) = (1 - p) * t := by ring
      have h2 : t * (0 - p) = -p * t := by ring
      rw [h1, h2]
      ring
    rw [hrew]
    exact hoeffding_lemma_bernoulli hp0 hp1 t
  have hnonneg : ∀ i : Fin k,
      0 ≤ ∑ b : Bool, bernWeight p b * Real.exp (t * (indBool b - p)) := by
    intro i
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (bernWeight_nonneg hp0 hp1 b) (le_of_lt (Real.exp_pos _))
  have hprod_le : ∀ (s : Finset (Fin k)) (u v : Fin k → ℝ),
      (∀ i ∈ s, 0 ≤ u i) → (∀ i ∈ s, u i ≤ v i) → ∏ i ∈ s, u i ≤ ∏ i ∈ s, v i := by
    intro s u v hu huv
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha0 : 0 ≤ u a := hu a (Finset.mem_insert_self a s)
      have ha_le : u a ≤ v a := huv a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∏ i ∈ s, u i :=
        Finset.prod_nonneg (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      have hs_le : ∏ i ∈ s, u i ≤ ∏ i ∈ s, v i :=
        ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
           (fun i hi => huv i (Finset.mem_insert_of_mem hi))
      have hva0 : 0 ≤ v a := le_trans ha0 ha_le
      exact mul_le_mul ha_le hs_le hs0 hva0
  calc ∏ i : Fin k, ∑ b : Bool, bernWeight p b * Real.exp (t * (indBool b - p))
      ≤ ∏ _i : Fin k, Real.exp (t ^ 2 / 8) :=
        hprod_le Finset.univ _ _ (fun i _ => hnonneg i) (fun i _ => hsingle i)
    _ = Real.exp ((k : ℝ) * t ^ 2 / 8) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
        congr 1
        ring

/-- Upper-tail Hoeffding inequality: `Pr(empComp - p ≥ ε) ≤ exp (-2 * k * ε ^ 2)`. -/
theorem hoeffding_upper_tail {k : ℕ} (hk : 0 < k) {p ε : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ empComp ω - p),
        bernProb p ω ≤ Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  let t : ℝ := 4 * ε
  have ht : 0 ≤ t := by positivity
  have hsum_eq : ∀ ω : Fin k → Bool,
      ∑ i : Fin k, (indBool (ω i) - p) = (k : ℝ) * (empComp ω - p) := by
    intro ω
    unfold empComp
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hkne]
  have hmarkov :
      Real.exp (t * (k : ℝ) * ε) *
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ empComp ω - p), bernProb p ω ≤
      ∑ ω : Fin k → Bool, bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) := by
    rw [Finset.mul_sum]
    calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ empComp ω - p),
            Real.exp (t * (k : ℝ) * ε) * bernProb p ω
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ empComp ω - p),
            bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) := by
          apply Finset.sum_le_sum
          intro ω hω
          have hge : ε ≤ empComp ω - p := (Finset.mem_filter.mp hω).2
          rw [hsum_eq ω, mul_comm (Real.exp (t * (k : ℝ) * ε))]
          apply mul_le_mul_of_nonneg_left _ (bernProb_nonneg hp0 hp1 ω)
          apply Real.exp_le_exp.mpr
          have htk : 0 ≤ t * (k : ℝ) := by positivity
          nlinarith
      _ ≤ ∑ ω : Fin k → Bool,
            bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro ω
          exact mul_nonneg (bernProb_nonneg hp0 hp1 ω) (le_of_lt (Real.exp_pos _))
  have hmgf := mgf_bound_bernoulli_sum (k := k) hp0 hp1 t
  have hcomb := le_trans hmarkov hmgf
  have hmul := mul_le_mul_of_nonneg_left hcomb (le_of_lt (Real.exp_pos (-(t * (k : ℝ) * ε))))
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hmul
  rw [← Real.exp_add] at hmul
  convert hmul using 2
  dsimp [t]
  ring

/-- Lower-tail Hoeffding inequality: `Pr(p - empComp ≥ ε) ≤ exp (-2 * k * ε ^ 2)`. -/
theorem hoeffding_lower_tail {k : ℕ} (hk : 0 < k) {p ε : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ p - empComp ω),
        bernProb p ω ≤ Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  let t : ℝ := -4 * ε
  have hsum_eq : ∀ ω : Fin k → Bool,
      ∑ i : Fin k, (indBool (ω i) - p) = (k : ℝ) * (empComp ω - p) := by
    intro ω
    unfold empComp
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hkne]
  have hmarkov :
      Real.exp (4 * ε * (k : ℝ) * ε) *
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ p - empComp ω), bernProb p ω ≤
      ∑ ω : Fin k → Bool, bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) := by
    rw [Finset.mul_sum]
    calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ p - empComp ω),
            Real.exp (4 * ε * (k : ℝ) * ε) * bernProb p ω
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ p - empComp ω),
            bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) := by
          apply Finset.sum_le_sum
          intro ω hω
          have hge : ε ≤ p - empComp ω := (Finset.mem_filter.mp hω).2
          rw [hsum_eq ω, mul_comm (Real.exp (4 * ε * (k : ℝ) * ε))]
          apply mul_le_mul_of_nonneg_left _ (bernProb_nonneg hp0 hp1 ω)
          apply Real.exp_le_exp.mpr
          have h4ek : 0 ≤ 4 * ε * (k : ℝ) := by positivity
          dsimp [t]
          nlinarith
      _ ≤ ∑ ω : Fin k → Bool,
            bernProb p ω * Real.exp (t * (∑ i : Fin k, (indBool (ω i) - p))) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro ω
          exact mul_nonneg (bernProb_nonneg hp0 hp1 ω) (le_of_lt (Real.exp_pos _))
  have hmgf := mgf_bound_bernoulli_sum (k := k) hp0 hp1 t
  have hcomb := le_trans hmarkov hmgf
  have hmul := mul_le_mul_of_nonneg_left hcomb (le_of_lt (Real.exp_pos (-(4 * ε * (k : ℝ) * ε))))
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hmul
  rw [← Real.exp_add] at hmul
  convert hmul using 2
  dsimp [t]
  ring

/-- **Two-Sided Exponential Hoeffding Concentration Bound** for MAG completeness:
with `k` independent collocated marker sets,
`Pr(|empComp - p| ≥ ε) ≤ 2 * exp (-2 * k * ε ^ 2)`. -/
theorem hoeffding_completeness_bound {k : ℕ} (hk : 0 < k) {p ε : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
        bernProb p ω ≤ 2 * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  let S_abs := Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|)
  let S_up := Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ empComp ω - p)
  let S_lo := Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ p - empComp ω)
  have hsub : S_abs ⊆ S_up ∪ S_lo := by
    intro ω hω
    simp only [S_abs, S_up, S_lo, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at hω ⊢
    rcases le_abs.mp hω with h | h
    · left; exact h
    · right; linarith
  calc ∑ ω ∈ S_abs, bernProb p ω
      ≤ ∑ ω ∈ S_up ∪ S_lo, bernProb p ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => bernProb_nonneg hp0 hp1 ω)
    _ ≤ (∑ ω ∈ S_up, bernProb p ω) + (∑ ω ∈ S_lo, bernProb p ω) := by
        have hui := Finset.sum_union_inter (s₁ := S_up) (s₂ := S_lo) (f := bernProb p)
        have hinter : 0 ≤ ∑ ω ∈ S_up ∩ S_lo, bernProb p ω :=
          Finset.sum_nonneg (fun ω _ => bernProb_nonneg hp0 hp1 ω)
        linarith
    _ ≤ Real.exp (-2 * (k : ℝ) * ε ^ 2) + Real.exp (-2 * (k : ℝ) * ε ^ 2) :=
        add_le_add (hoeffding_upper_tail hk hp0 hp1 hε) (hoeffding_lower_tail hk hp0 hp1 hε)
    _ = 2 * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by ring

/-- **Certified Hoeffding Radius** for `k` independent marker sets at failure rate `δ`:
`hoeffdingRadius k δ = √(log (2 / δ) / (2 * k))`. -/
noncomputable def hoeffdingRadius (k : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (Real.log (2 / δ) / (2 * (k : ℝ)))

/-- **Marker-Count Sample-Size Guarantee**: If the number of independent collocated
marker sets satisfies `k ≥ log (2 / δ) / (2 * ε ^ 2)`, then empirical completeness
stays within `± ε` of true completeness `p` with probability at least `1 - δ`. -/
theorem marker_count_sufficient {k : ℕ} (hk : 0 < k) {p ε δ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hδ : 0 < δ)
    (hsize : Real.log (2 / δ) / (2 * ε ^ 2) ≤ (k : ℝ)) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ε ≤ |empComp ω - p|),
        bernProb p ω ≤ δ := by
  have h1 := hoeffding_completeness_bound hk hp0 hp1 (le_of_lt hε)
  have h2ε2 : 0 < 2 * ε ^ 2 := by positivity
  have hlog_le : Real.log (2 / δ) ≤ 2 * (k : ℝ) * ε ^ 2 := by
    have := (div_le_iff₀ h2ε2).mp hsize
    linarith
  have hexp_le : Real.exp (-2 * (k : ℝ) * ε ^ 2) ≤ δ / 2 := by
    have hneg : -2 * (k : ℝ) * ε ^ 2 ≤ Real.log (δ / 2) := by
      have hinv : Real.log (δ / 2) = -Real.log (2 / δ) := by
        rw [Real.log_div (ne_of_gt hδ) (by norm_num),
            Real.log_div (by norm_num) (ne_of_gt hδ)]
        ring
      linarith
    calc Real.exp (-2 * (k : ℝ) * ε ^ 2)
        ≤ Real.exp (Real.log (δ / 2)) := Real.exp_le_exp.mpr hneg
      _ = δ / 2 := Real.exp_log (by positivity)
  linarith

/-- **Taxonomic Resolution Gain Theorem**: Moving down a taxonomy to a lineage-specific
marker family with strictly more independent marker sets (`k₁ < k₂`) strictly shrinks
the certified Hoeffding confidence radius (for `δ ∈ (0, 2)`). -/
theorem hoeffdingRadius_strict_shrink {k₁ k₂ : ℕ} {δ : ℝ}
    (hk₁ : 0 < k₁) (hlt : k₁ < k₂) (hδ0 : 0 < δ) (hδ2 : δ < 2) :
    hoeffdingRadius k₂ δ < hoeffdingRadius k₁ δ := by
  unfold hoeffdingRadius
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos ((one_lt_div hδ0).mpr hδ2)
  have hk₁r : (0 : ℝ) < (k₁ : ℝ) := Nat.cast_pos.mpr hk₁
  have hklt : (k₁ : ℝ) < (k₂ : ℝ) := Nat.cast_lt.mpr hlt
  have hfrac : Real.log (2 / δ) / (2 * (k₂ : ℝ)) < Real.log (2 / δ) / (2 * (k₁ : ℝ)) :=
    div_lt_div_of_pos_left hlog (by positivity) (by linarith)
  exact Real.sqrt_lt_sqrt (by positivity) hfrac

/-! ### Exact Chimeric Masking Expectation Model -/

/-- Expected observed completeness when target genome (completeness `p`) is merged
with an independent foreign contaminant (completeness `q`): `p + q - p * q`. -/
def expectedChimericComp (p q : ℝ) : ℝ := p + q - p * q

/-- Expected observed marker contamination under the same model: `p * q`. -/
def expectedChimericCont (p q : ℝ) : ℝ := p * q

/-- Exact derivation over a single independent marker hit pair `(target, contam)`. -/
theorem single_marker_chimeric_expectation (p q : ℝ) :
    (∑ a : Bool, ∑ b : Bool,
      bernWeight p a * bernWeight q b * (if a || b then (1 : ℝ) else 0)) =
      expectedChimericComp p q ∧
    (∑ a : Bool, ∑ b : Bool,
      bernWeight p a * bernWeight q b * (if a && b then (1 : ℝ) else 0)) =
      expectedChimericCont p q := by
  constructor
  · simp [bernWeight, expectedChimericComp]; ring
  · simp [bernWeight, expectedChimericCont]

/-- **Artificial Completeness Inflation**: Foreign contamination `q` inflates
expected apparent completeness by `q * (1 - p) ≥ 0`. -/
theorem chimeric_completeness_inflation {p q : ℝ} (hp1 : p ≤ 1) (hq0 : 0 ≤ q) :
    expectedChimericComp p q - p = q * (1 - p) ∧ 0 ≤ expectedChimericComp p q - p := by
  unfold expectedChimericComp
  constructor
  · ring
  · nlinarith

/-- **Contamination Underestimation Law**: Only fraction `p` of foreign completeness `q`
triggers a duplicate marker hit; fraction `1 - p` is hidden as apparent completeness! -/
theorem chimeric_contamination_hidden (p q : ℝ) :
    q - expectedChimericCont p q = q * (1 - p) ∧
      expectedChimericComp p q + expectedChimericCont p q = p + q := by
  unfold expectedChimericComp expectedChimericCont
  constructor <;> ring

/-- **Explicit MIMAG Medium-Quality Evasion Witness**:
A 50%-complete target genome contaminated with an 18%-complete foreign genome achieves
expected completeness `59% ≥ 50%` and expected contamination `9% < 10%`! -/
theorem mimag_mq_evasion_expectation :
    expectedChimericComp (1 / 2) (18 / 100) = 59 / 100 ∧
    expectedChimericCont (1 / 2) (18 / 100) = 9 / 100 ∧
    (1 / 2 : ℝ) ≤ expectedChimericComp (1 / 2) (18 / 100) ∧
    expectedChimericCont (1 / 2) (18 / 100) < 1 / 10 := by
  unfold expectedChimericComp expectedChimericCont
  norm_num

end

end MAGLean.Probabilistic
