import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# MAGLean.Dereplication

Formal mathematical theory of Average Nucleotide Identity (ANI), Aligned Fraction (AF),
and species-cluster dereplication guarantees (fastANI / dRep / GTDB).

## Main Results

* `ani_triangle_inequality_counterexample`: Constructive 3-genome witness showing that
  ANI fails the triangle inequality when aligned fractions do not overlap (`AF = 1/2`,
  `ANI(G₁, G₂) = 1`, `ANI(G₂, G₃) = 1`, yet `ANI(G₁, G₃) = 0`).
* `ani_core_overlap_theorem`: **Overlap-Conditioned Relaxed Triangle Inequality** —
  whenever `AF₁₂ + AF₂₃ > 1`, the mutual core `A₁₂ ∩ A₂₃` has fraction at least
  `AF₁₂ + AF₂₃ - 1 > 0`, and core divergence satisfies
  `d_core(G₁, G₃) ≤ (AF₁₂ * d₁₂ + AF₂₃ * d₂₃) / (AF₁₂ + AF₂₃ - 1)`,
  equivalently
  `ANI_core(G₁, G₃) ≥ 1 - (AF₁₂ * (1 - ANI₁₂) + AF₂₃ * (1 - ANI₂₃)) / (AF₁₂ + AF₂₃ - 1)`.
* `derep_cluster_diameter_bound`: If every genome in a dereplication cluster aligns to
  representative `R` with `AF ≥ f > 1/2` and `ANI ≥ 1 - δ`, then *every pair* of genomes
  in the cluster shares core fraction `≥ 2 * f - 1` with core `ANI ≥ 1 - (2 * f * δ) / (2 * f - 1)`.
* `derep_80_97_corollary`: Numeric certification — at `AF ≥ 80%` and `ANI ≥ 97%` to a
  representative, every intra-cluster pair shares `≥ 60%` core with `≥ 92%` core ANI.
-/

namespace MAGLean.Dereplication

section AlignmentModel

variable {Locus Base : Type*} [DecidableEq Locus] [DecidableEq Base]

/-- Aligned fraction of locus subset `A ⊆ S` relative to reference genome loci `S`. -/
def alignedFraction (S A : Finset Locus) : ℚ :=
  (A.card : ℚ) / (S.card : ℚ)

/-- Set of mismatching loci between two genomes `g₁, g₂` within aligned region `A`. -/
def mismatchSet (A : Finset Locus) (g₁ g₂ : Locus → Base) : Finset Locus :=
  A.filter (fun i => g₁ i ≠ g₂ i)

/-- Divergence (`1 - ANI`) between `g₁` and `g₂` over aligned region `A`. -/
def divergence (A : Finset Locus) (g₁ g₂ : Locus → Base) : ℚ :=
  ((mismatchSet A g₁ g₂).card : ℚ) / (A.card : ℚ)

/-- Average Nucleotide Identity (ANI) between `g₁` and `g₂` over aligned region `A`. -/
def ani (A : Finset Locus) (g₁ g₂ : Locus → Base) : ℚ :=
  1 - divergence A g₁ g₂

lemma mismatchSet_triangle (I : Finset Locus) (g₁ g₂ g₃ : Locus → Base) :
    mismatchSet I g₁ g₃ ⊆ mismatchSet I g₁ g₂ ∪ mismatchSet I g₂ g₃ := by
  intro i hi
  simp only [mismatchSet, Finset.mem_union, Finset.mem_filter] at hi ⊢
  by_cases h : g₁ i = g₂ i
  · right
    refine ⟨hi.1, ?_⟩
    intro h23
    exact hi.2 (h.trans h23)
  · left
    exact ⟨hi.1, h⟩

omit [DecidableEq Locus] in
lemma mismatchSet_mono {I A : Finset Locus} (hsub : I ⊆ A) (g₁ g₂ : Locus → Base) :
    mismatchSet I g₁ g₂ ⊆ mismatchSet A g₁ g₂ := by
  intro i hi
  simp only [mismatchSet, Finset.mem_filter] at hi ⊢
  exact ⟨hsub hi.1, hi.2⟩

lemma core_card_lower_bound {S A₁₂ A₂₃ : Finset Locus}
    (h1 : A₁₂ ⊆ S) (h2 : A₂₃ ⊆ S) :
    ((A₁₂.card : ℚ) + (A₂₃.card : ℚ)) - (S.card : ℚ) ≤ ((A₁₂ ∩ A₂₃).card : ℚ) := by
  have hunion_sub : A₁₂ ∪ A₂₃ ⊆ S := Finset.union_subset h1 h2
  have hunion_card : (A₁₂ ∪ A₂₃).card ≤ S.card := Finset.card_le_card hunion_sub
  have hiu := Finset.card_union_add_card_inter A₁₂ A₂₃
  have hiu_q : ((A₁₂ ∪ A₂₃).card : ℚ) + ((A₁₂ ∩ A₂₃).card : ℚ) =
      (A₁₂.card : ℚ) + (A₂₃.card : ℚ) := by exact_mod_cast hiu
  have hunion_q : ((A₁₂ ∪ A₂₃).card : ℚ) ≤ (S.card : ℚ) := by exact_mod_cast hunion_card
  linarith

/-- **Overlap-Conditioned Relaxed Triangle Inequality (Core-Overlap Theorem)**:
Let `S` be the reference loci of genome `g₂`, and let `A₁₂, A₂₃ ⊆ S` be the aligned
regions with `g₁` and `g₃` respectively. Whenever `AF₁₂ + AF₂₃ > 1`, the mutual core
`I = A₁₂ ∩ A₂₃` satisfies:
1. `alignedFraction S I ≥ AF₁₂ + AF₂₃ - 1 > 0`
2. `divergence I g₁ g₃ ≤ (AF₁₂ * d₁₂ + AF₂₃ * d₂₃) / (AF₁₂ + AF₂₃ - 1)`
3. `ani I g₁ g₃ ≥ 1 - (AF₁₂ * (1 - ANI₁₂) + AF₂₃ * (1 - ANI₂₃)) / (AF₁₂ + AF₂₃ - 1)`. -/
theorem ani_core_overlap_theorem
    {S A₁₂ A₂₃ : Finset Locus} (hS : S.Nonempty)
    (hsub1 : A₁₂ ⊆ S) (hsub2 : A₂₃ ⊆ S)
    (hoverlap : 1 < alignedFraction S A₁₂ + alignedFraction S A₂₃)
    (g₁ g₂ g₃ : Locus → Base) :
    let I := A₁₂ ∩ A₂₃
    let f₁₂ := alignedFraction S A₁₂
    let f₂₃ := alignedFraction S A₂₃
    let d₁₂ := divergence A₁₂ g₁ g₂
    let d₂₃ := divergence A₂₃ g₂ g₃
    0 < f₁₂ + f₂₃ - 1 ∧
    f₁₂ + f₂₃ - 1 ≤ alignedFraction S I ∧
    divergence I g₁ g₃ ≤ (f₁₂ * d₁₂ + f₂₃ * d₂₃) / (f₁₂ + f₂₃ - 1) ∧
    1 - (f₁₂ * (1 - ani A₁₂ g₁ g₂) + f₂₃ * (1 - ani A₂₃ g₂ g₃)) / (f₁₂ + f₂₃ - 1) ≤
      ani I g₁ g₃ := by
  intro I f₁₂ f₂₃ d₁₂ d₂₃
  have hSpos : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast hS.card_pos
  have hSne : (S.card : ℚ) ≠ 0 := ne_of_gt hSpos
  have hgap : 0 < f₁₂ + f₂₃ - 1 := by linarith
  -- Core fraction lower bound
  have hcore_frac : f₁₂ + f₂₃ - 1 ≤ alignedFraction S I := by
    dsimp [f₁₂, f₂₃, I, alignedFraction]
    have hcard := core_card_lower_bound hsub1 hsub2
    have hdiv := div_le_div_of_nonneg_right hcard (le_of_lt hSpos)
    calc (A₁₂.card : ℚ) / (S.card : ℚ) + (A₂₃.card : ℚ) / (S.card : ℚ) - 1
        = ((A₁₂.card : ℚ) + (A₂₃.card : ℚ) - (S.card : ℚ)) / (S.card : ℚ) := by
          field_simp [hSne]
      _ ≤ ((A₁₂ ∩ A₂₃).card : ℚ) / (S.card : ℚ) := hdiv
  have hI_pos : (0 : ℚ) < (I.card : ℚ) := by
    have h1 : (0 : ℚ) < alignedFraction S I := lt_of_lt_of_le hgap hcore_frac
    dsimp [alignedFraction] at h1
    exact (div_pos_iff_of_pos_right hSpos).mp h1
  -- Mismatch count triangle bound on the core `I`
  have hmism_sub :
      mismatchSet I g₁ g₃ ⊆ mismatchSet A₁₂ g₁ g₂ ∪ mismatchSet A₂₃ g₂ g₃ := by
    calc mismatchSet I g₁ g₃
        ⊆ mismatchSet I g₁ g₂ ∪ mismatchSet I g₂ g₃ := mismatchSet_triangle I g₁ g₂ g₃
      _ ⊆ mismatchSet A₁₂ g₁ g₂ ∪ mismatchSet A₂₃ g₂ g₃ :=
          Finset.union_subset_union
            (mismatchSet_mono Finset.inter_subset_left g₁ g₂)
            (mismatchSet_mono Finset.inter_subset_right g₂ g₃)
  have hmism_card :
      ((mismatchSet I g₁ g₃).card : ℚ) ≤
        ((mismatchSet A₁₂ g₁ g₂).card : ℚ) + ((mismatchSet A₂₃ g₂ g₃).card : ℚ) := by
    have hnat : (mismatchSet I g₁ g₃).card ≤
        (mismatchSet A₁₂ g₁ g₂).card + (mismatchSet A₂₃ g₂ g₃).card :=
      le_trans (Finset.card_le_card hmism_sub) (Finset.card_union_le _ _)
    exact_mod_cast hnat
  -- Express `f₁₂ * d₁₂` and `f₂₃ * d₂₃` in terms of mismatch counts
  have hfd1 : f₁₂ * d₁₂ = ((mismatchSet A₁₂ g₁ g₂).card : ℚ) / (S.card : ℚ) := by
    dsimp [f₁₂, d₁₂, alignedFraction, divergence]
    by_cases hA : A₁₂.card = 0
    · have hempty : A₁₂ = ∅ := Finset.card_eq_zero.mp hA
      simp [hempty, mismatchSet]
    · have hAne : (A₁₂.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA
      field_simp [hSne, hAne]
  have hfd2 : f₂₃ * d₂₃ = ((mismatchSet A₂₃ g₂ g₃).card : ℚ) / (S.card : ℚ) := by
    dsimp [f₂₃, d₂₃, alignedFraction, divergence]
    by_cases hA : A₂₃.card = 0
    · have hempty : A₂₃ = ∅ := Finset.card_eq_zero.mp hA
      simp [hempty, mismatchSet]
    · have hAne : (A₂₃.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA
      field_simp [hSne, hAne]
  have hdiv_bound : divergence I g₁ g₃ ≤ (f₁₂ * d₁₂ + f₂₃ * d₂₃) / (f₁₂ + f₂₃ - 1) := by
    have hnum_le : ((mismatchSet I g₁ g₃).card : ℚ) / (S.card : ℚ) ≤ f₁₂ * d₁₂ + f₂₃ * d₂₃ := by
      rw [hfd1, hfd2, ← add_div]
      exact div_le_div_of_nonneg_right hmism_card (le_of_lt hSpos)
    have hI_frac_pos : 0 < alignedFraction S I := lt_of_lt_of_le hgap hcore_frac
    have hdiv_rew : divergence I g₁ g₃ =
        (((mismatchSet I g₁ g₃).card : ℚ) / (S.card : ℚ)) / alignedFraction S I := by
      dsimp [divergence, alignedFraction]
      field_simp [hSne, ne_of_gt hI_pos]
    rw [hdiv_rew]
    calc (((mismatchSet I g₁ g₃).card : ℚ) / (S.card : ℚ)) / alignedFraction S I
        ≤ (f₁₂ * d₁₂ + f₂₃ * d₂₃) / alignedFraction S I :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hI_frac_pos)
      _ ≤ (f₁₂ * d₁₂ + f₂₃ * d₂₃) / (f₁₂ + f₂₃ - 1) := by
          have hnn : 0 ≤ f₁₂ * d₁₂ + f₂₃ * d₂₃ := by
            rw [hfd1, hfd2]; positivity
          exact div_le_div_of_nonneg_left hnn hgap hcore_frac
  have hani_bound :
      1 - (f₁₂ * (1 - ani A₁₂ g₁ g₂) + f₂₃ * (1 - ani A₂₃ g₂ g₃)) / (f₁₂ + f₂₃ - 1) ≤
        ani I g₁ g₃ := by
    have h1 : 1 - ani A₁₂ g₁ g₂ = d₁₂ := by dsimp [ani, d₁₂]; ring
    have h2 : 1 - ani A₂₃ g₂ g₃ = d₂₃ := by dsimp [ani, d₂₃]; ring
    rw [h1, h2]
    dsimp [ani]
    linarith
  exact ⟨hgap, hcore_frac, hdiv_bound, hani_bound⟩

/-- **Representative Cluster Diameter Bound**: If two genomes `g₁, g₃` both align to a
dereplication cluster representative `g₂` with aligned fraction at least `f > 1/2` and
`ANI ≥ 1 - δ`, then `g₁` and `g₃` are guaranteed to share core fraction `≥ 2 * f - 1`
with core `ANI ≥ 1 - (2 * f * δ) / (2 * f - 1)`. -/
theorem derep_cluster_diameter_bound
    {S A₁₂ A₂₃ : Finset Locus} (hS : S.Nonempty)
    (hsub1 : A₁₂ ⊆ S) (hsub2 : A₂₃ ⊆ S)
    {f δ : ℚ} (hf : 1 / 2 < f) (hδ : 0 ≤ δ)
    (hf1 : f ≤ alignedFraction S A₁₂) (hf2 : f ≤ alignedFraction S A₂₃)
    (g₁ g₂ g₃ : Locus → Base)
    (ha1 : 1 - δ ≤ ani A₁₂ g₁ g₂) (ha2 : 1 - δ ≤ ani A₂₃ g₂ g₃) :
    let I := A₁₂ ∩ A₂₃
    2 * f - 1 ≤ alignedFraction S I ∧
    1 - (2 * f * δ) / (2 * f - 1) ≤ ani I g₁ g₃ := by
  intro I
  have hoverlap : 1 < alignedFraction S A₁₂ + alignedFraction S A₂₃ := by linarith
  have hcore := ani_core_overlap_theorem hS hsub1 hsub2 hoverlap g₁ g₂ g₃
  rcases hcore with ⟨hgap, hcore_frac, hdiv_bound, _⟩
  have h2f : 0 < 2 * f - 1 := by linarith
  have hf1_le1 : alignedFraction S A₁₂ ≤ 1 := by
    unfold alignedFraction
    rw [div_le_one (by exact_mod_cast hS.card_pos)]
    exact_mod_cast Finset.card_le_card hsub1
  have hf2_le1 : alignedFraction S A₂₃ ≤ 1 := by
    unfold alignedFraction
    rw [div_le_one (by exact_mod_cast hS.card_pos)]
    exact_mod_cast Finset.card_le_card hsub2
  have hd1 : divergence A₁₂ g₁ g₂ ≤ δ := by unfold ani at ha1; linarith
  have hd2 : divergence A₂₃ g₂ g₃ ≤ δ := by unfold ani at ha2; linarith
  have hd1_nn : 0 ≤ divergence A₁₂ g₁ g₂ := by unfold divergence; positivity
  have hd2_nn : 0 ≤ divergence A₂₃ g₂ g₃ := by unfold divergence; positivity
  have hcore_2f : 2 * f - 1 ≤ alignedFraction S I := by linarith
  -- Key monotonicity: `(x + y) / (x + y - 1)` is decreasing in `x + y > 1`!
  have hsum_ge : 2 * f ≤ alignedFraction S A₁₂ + alignedFraction S A₂₃ := by linarith
  have hratio :
      (alignedFraction S A₁₂ + alignedFraction S A₂₃) /
          (alignedFraction S A₁₂ + alignedFraction S A₂₃ - 1) ≤
        (2 * f) / (2 * f - 1) := by
    rw [div_le_div_iff₀ hgap h2f]
    nlinarith
  have hnum_le :
      alignedFraction S A₁₂ * divergence A₁₂ g₁ g₂ +
          alignedFraction S A₂₃ * divergence A₂₃ g₂ g₃ ≤
        (alignedFraction S A₁₂ + alignedFraction S A₂₃) * δ := by
    have hf1_nn : 0 ≤ alignedFraction S A₁₂ := by unfold alignedFraction; positivity
    have hf2_nn : 0 ≤ alignedFraction S A₂₃ := by unfold alignedFraction; positivity
    nlinarith
  have hdiv_final : divergence I g₁ g₃ ≤ (2 * f * δ) / (2 * f - 1) := by
    calc divergence I g₁ g₃
        ≤ (alignedFraction S A₁₂ * divergence A₁₂ g₁ g₂ +
            alignedFraction S A₂₃ * divergence A₂₃ g₂ g₃) /
              (alignedFraction S A₁₂ + alignedFraction S A₂₃ - 1) := hdiv_bound
      _ ≤ ((alignedFraction S A₁₂ + alignedFraction S A₂₃) * δ) /
            (alignedFraction S A₁₂ + alignedFraction S A₂₃ - 1) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hgap)
      _ = ((alignedFraction S A₁₂ + alignedFraction S A₂₃) /
            (alignedFraction S A₁₂ + alignedFraction S A₂₃ - 1)) * δ := by ring
      _ ≤ ((2 * f) / (2 * f - 1)) * δ :=
          mul_le_mul_of_nonneg_right hratio hδ
      _ = (2 * f * δ) / (2 * f - 1) := by ring
  refine ⟨hcore_2f, ?_⟩
  unfold ani
  linarith

/-- **Concrete Dereplication Certification (`AF ≥ 80%`, `ANI ≥ 97%`)**:
If two cluster members both align to the representative at `AF ≥ 4/5` and `ANI ≥ 97/100`,
they are mathematically guaranteed to share `≥ 60%` core fraction with `≥ 92%` core ANI. -/
theorem derep_80_97_corollary
    {S A₁₂ A₂₃ : Finset Locus} (hS : S.Nonempty)
    (hsub1 : A₁₂ ⊆ S) (hsub2 : A₂₃ ⊆ S)
    (hf1 : (4 / 5 : ℚ) ≤ alignedFraction S A₁₂)
    (hf2 : (4 / 5 : ℚ) ≤ alignedFraction S A₂₃)
    (g₁ g₂ g₃ : Locus → Base)
    (ha1 : (97 / 100 : ℚ) ≤ ani A₁₂ g₁ g₂)
    (ha2 : (97 / 100 : ℚ) ≤ ani A₂₃ g₂ g₃) :
    (3 / 5 : ℚ) ≤ alignedFraction S (A₁₂ ∩ A₂₃) ∧
    (92 / 100 : ℚ) ≤ ani (A₁₂ ∩ A₂₃) g₁ g₃ := by
  have h := derep_cluster_diameter_bound hS hsub1 hsub2 (f := 4 / 5) (δ := 3 / 100)
    (by norm_num) (by norm_num) hf1 hf2 g₁ g₂ g₃
    (by norm_num; exact ha1) (by norm_num; exact ha2)
  rcases h with ⟨h1, h2⟩
  constructor <;> linarith

end AlignmentModel

/-- **Constructive ANI Triangle-Inequality Failure (Chimeric Bridge Counterexample)**:
There exist genomes `g₁, g₂, g₃` over a 2-locus reference `S = {0, 1}` such that
`g₁` matches `g₂` with `ANI = 1` on `AF = 1/2`, `g₂` matches `g₃` with `ANI = 1` on
`AF = 1/2`, yet `g₁` and `g₃` disagree on *every* locus (`ANI(S, g₁, g₃) = 0`). -/
theorem ani_triangle_inequality_counterexample :
    ∃ (S A₁₂ A₂₃ : Finset (Fin 2)) (g₁ g₂ g₃ : Fin 2 → Bool),
      A₁₂ ⊆ S ∧ A₂₃ ⊆ S ∧
      alignedFraction S A₁₂ = 1 / 2 ∧
      alignedFraction S A₂₃ = 1 / 2 ∧
      ani A₁₂ g₁ g₂ = 1 ∧
      ani A₂₃ g₂ g₃ = 1 ∧
      ani S g₁ g₃ = 0 := by
  refine ⟨Finset.univ, {0}, {1},
    (fun _ => false),
    (fun i => if i = 0 then false else true),
    (fun _ => true),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.subset_univ _
  · exact Finset.subset_univ _
  · simp [alignedFraction]
  · simp [alignedFraction]
  · simp [ani, divergence, mismatchSet]
  · simp [ani, divergence, mismatchSet]
  · simp [ani, divergence, mismatchSet]

end MAGLean.Dereplication
