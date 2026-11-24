import MAGLean.Basic

/-!
# MAGLean.Markers

Exact algebraic theory of marker-based MAG completeness, contamination, and
chimerism for collocated marker families (CheckM model).

## Main Results

* `comp_add_cont_eq_mass`: `completeness M f + contamination M f = markerMass M f`.
* `conservation_law`: Total marker mass (`completeness + contamination`) is strictly
  additive across disjoint bin unions (`f₁ + f₂`).
* `cont_add_eq`: Cross-contamination created by merging `f₁` and `f₂` equals
  `sharedCompleteness M f₁ f₂` identically.
* `comp_add_eq`: Inclusion-exclusion for completeness under bin merging.
* `split_completeness_ceiling`: For any split `f₁ + f₂`,
  `comp(f₁) + comp(f₂) ≤ comp(f₁ + f₂) + cont(f₁ + f₂)`.
* `chimeric_masking_identity`: Hidden contamination from a foreign genome converts
  1-for-1 into artificial completeness inflation.
* `stealth_chimera_exists`: Constructive impossibility theorem—for *every* marker
  family with at least 2 distinct markers, two completely disjoint pure genomes merge
  into a 100%-complete, 0%-contaminated chimeric MAG.
* `accessory_invariance`: Adding/removing marker-free contigs (plasmids, prophages,
  accessory islands) leaves both completeness and contamination strictly unchanged.
-/

namespace MAGLean

section SingleSetLemmas

variable {α : Type*}

/-- Completeness contribution of a single collocated marker set `s`. -/
def setComp (s : Finset α) (f : α → ℕ) : ℚ :=
  (∑ g ∈ s, (present (f g) : ℚ)) / (s.card : ℚ)

/-- Contamination contribution of a single collocated marker set `s`. -/
def setCont (s : Finset α) (f : α → ℕ) : ℚ :=
  (∑ g ∈ s, (excess (f g) : ℚ)) / (s.card : ℚ)

/-- Total weighted marker copy mass of a single collocated marker set `s`. -/
def setMass (s : Finset α) (f : α → ℕ) : ℚ :=
  (∑ g ∈ s, (f g : ℚ)) / (s.card : ℚ)

/-- Shared-marker overlap contribution of a single collocated marker set `s`. -/
def setShared (s : Finset α) (f₁ f₂ : α → ℕ) : ℚ :=
  (∑ g ∈ s, (shared (f₁ g) (f₂ g) : ℚ)) / (s.card : ℚ)

/-- CheckM-style collocated marker-set completeness (`∈ [0, 1]`). -/
def completeness [DecidableEq α] (M : MarkerFamily α) (f : α → ℕ) : ℚ :=
  (M.sets.map (fun s => setComp s f)).sum / (M.numSets : ℚ)

/-- CheckM-style collocated marker-set contamination (`≥ 0`). -/
def contamination [DecidableEq α] (M : MarkerFamily α) (f : α → ℕ) : ℚ :=
  (M.sets.map (fun s => setCont s f)).sum / (M.numSets : ℚ)

/-- Total weighted marker copy mass across a marker family. -/
def markerMass [DecidableEq α] (M : MarkerFamily α) (f : α → ℕ) : ℚ :=
  (M.sets.map (fun s => setMass s f)).sum / (M.numSets : ℚ)

/-- Weighted shared completeness between two copy-count profiles `f₁` and `f₂`. -/
def sharedCompleteness [DecidableEq α] (M : MarkerFamily α) (f₁ f₂ : α → ℕ) : ℚ :=
  (M.sets.map (fun s => setShared s f₁ f₂)).sum / (M.numSets : ℚ)

/-! ### Helper lemmas for `List.sum` -/

private lemma list_sum_map_add {β : Type*} (l : List β) (u v : β → ℚ) :
    (l.map (fun x => u x + v x)).sum = (l.map u).sum + (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma list_sum_map_nonneg {β : Type*} (l : List β) (u : β → ℚ)
    (h : ∀ x ∈ l, 0 ≤ u x) : 0 ≤ (l.map u).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx : 0 ≤ u x := h x (by simp)
    have hxs : 0 ≤ (xs.map u).sum := ih (fun y hy => h y (by simp [hy]))
    linarith

private lemma list_sum_map_le {β : Type*} (l : List β) (u v : β → ℚ)
    (h : ∀ x ∈ l, u x ≤ v x) : (l.map u).sum ≤ (l.map v).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx : u x ≤ v x := h x (by simp)
    have hxs : (xs.map u).sum ≤ (xs.map v).sum := ih (fun y hy => h y (by simp [hy]))
    linarith

private lemma list_sum_map_const {β : Type*} (l : List β) (c : ℚ) :
    (l.map (fun _ => c)).sum = (l.length : ℚ) * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

private lemma list_sum_map_pos_of_exists {β : Type*} (l : List β) (u : β → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ u x) (hex : ∃ x ∈ l, 0 < u x) :
    0 < (l.map u).sum := by
  induction l with
  | nil =>
    rcases hex with ⟨_, hmem, _⟩
    simp at hmem
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases hex with ⟨y, hy, hypos⟩
    rcases List.mem_cons.mp hy with rfl | hmem
    · have hxs : 0 ≤ (xs.map u).sum := list_sum_map_nonneg xs u (fun z hz => h0 z (by simp [hz]))
      linarith
    · have hx : 0 ≤ u x := h0 x (by simp)
      have hxs : 0 < (xs.map u).sum := ih (fun z hz => h0 z (by simp [hz])) ⟨y, hmem, hypos⟩
      linarith

/-! ### Single-set lemmas -/

lemma setComp_nonneg (s : Finset α) (f : α → ℕ) : 0 ≤ setComp s f := by
  unfold setComp
  positivity

lemma setCont_nonneg (s : Finset α) (f : α → ℕ) : 0 ≤ setCont s f := by
  unfold setCont
  positivity

lemma setShared_nonneg (s : Finset α) (f₁ f₂ : α → ℕ) : 0 ≤ setShared s f₁ f₂ := by
  unfold setShared
  positivity

lemma setComp_le_one (s : Finset α) (f : α → ℕ) : setComp s f ≤ 1 := by
  unfold setComp
  by_cases hs : s.card = 0
  · simp [hs]
  · have hpos : (0 : ℚ) < (s.card : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hs
    rw [div_le_one hpos]
    calc (∑ g ∈ s, (present (f g) : ℚ))
        ≤ ∑ _g ∈ s, (1 : ℚ) := by
          apply Finset.sum_le_sum
          intro g _
          exact_mod_cast present_le_one (f g)
      _ = (s.card : ℚ) := by simp

lemma setComp_mono (s : Finset α) {f₁ f₂ : α → ℕ} (h : ∀ g, f₁ g ≤ f₂ g) :
    setComp s f₁ ≤ setComp s f₂ := by
  unfold setComp
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast present_mono (h g)

lemma setCont_mono (s : Finset α) {f₁ f₂ : α → ℕ} (h : ∀ g, f₁ g ≤ f₂ g) :
    setCont s f₁ ≤ setCont s f₂ := by
  unfold setCont
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast excess_mono (h g)

lemma setComp_add_setCont (s : Finset α) (f : α → ℕ) :
    setComp s f + setCont s f = setMass s f := by
  unfold setComp setCont setMass
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact_mod_cast present_add_excess (f g)

lemma setMass_add (s : Finset α) (f₁ f₂ : α → ℕ) :
    setMass s (f₁ + f₂) = setMass s f₁ + setMass s f₂ := by
  unfold setMass
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  simp [Pi.add_apply]

lemma setComp_add_setShared (s : Finset α) (f₁ f₂ : α → ℕ) :
    setComp s (f₁ + f₂) + setShared s f₁ f₂ = setComp s f₁ + setComp s f₂ := by
  unfold setComp setShared
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  simp only [Pi.add_apply]
  exact_mod_cast present_add_shared (f₁ g) (f₂ g)

lemma setCont_add_eq (s : Finset α) (f₁ f₂ : α → ℕ) :
    setCont s (f₁ + f₂) = setCont s f₁ + setCont s f₂ + setShared s f₁ f₂ := by
  unfold setCont setShared
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  simp only [Pi.add_apply]
  exact_mod_cast excess_add_eq (f₁ g) (f₂ g)

lemma setShared_le_left (s : Finset α) (f₁ f₂ : α → ℕ) :
    setShared s f₁ f₂ ≤ setComp s f₁ := by
  unfold setShared setComp
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast shared_le_present_left (f₁ g) (f₂ g)

lemma setShared_le_right (s : Finset α) (f₁ f₂ : α → ℕ) :
    setShared s f₁ f₂ ≤ setComp s f₂ := by
  unfold setShared setComp
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast shared_le_present_right (f₁ g) (f₂ g)

lemma setShared_comm (s : Finset α) (f₁ f₂ : α → ℕ) :
    setShared s f₁ f₂ = setShared s f₂ f₁ := by
  unfold setShared
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact_mod_cast shared_comm (f₁ g) (f₂ g)

end SingleSetLemmas

section FamilyTheorems

variable {α : Type*} [DecidableEq α]

/-! ### Family-level theorems -/

theorem completeness_nonneg (M : MarkerFamily α) (f : α → ℕ) :
    0 ≤ completeness M f := by
  unfold completeness
  apply div_nonneg
  · exact list_sum_map_nonneg M.sets (fun s => setComp s f) (fun s _ => setComp_nonneg s f)
  · positivity

theorem completeness_le_one (M : MarkerFamily α) (f : α → ℕ) :
    completeness M f ≤ 1 := by
  unfold completeness
  have hpos := M.numSets_pos_rat
  rw [div_le_one hpos]
  calc (M.sets.map (fun s => setComp s f)).sum
      ≤ (M.sets.map (fun _ => (1 : ℚ))).sum :=
        list_sum_map_le M.sets _ _ (fun s _ => setComp_le_one s f)
    _ = (M.numSets : ℚ) := by
        rw [list_sum_map_const, mul_one]; rfl

theorem contamination_nonneg (M : MarkerFamily α) (f : α → ℕ) :
    0 ≤ contamination M f := by
  unfold contamination
  apply div_nonneg
  · exact list_sum_map_nonneg M.sets (fun s => setCont s f) (fun s _ => setCont_nonneg s f)
  · positivity

theorem sharedCompleteness_nonneg (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    0 ≤ sharedCompleteness M f₁ f₂ := by
  unfold sharedCompleteness
  apply div_nonneg
  · exact list_sum_map_nonneg M.sets (fun s => setShared s f₁ f₂) (fun s _ => setShared_nonneg s f₁ f₂)
  · positivity

theorem sharedCompleteness_comm (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    sharedCompleteness M f₁ f₂ = sharedCompleteness M f₂ f₁ := by
  unfold sharedCompleteness
  congr 1
  congr 1
  apply List.map_congr_left
  intro s _
  exact setShared_comm s f₁ f₂

theorem sharedCompleteness_le_left (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    sharedCompleteness M f₁ f₂ ≤ completeness M f₁ := by
  unfold sharedCompleteness completeness
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact list_sum_map_le M.sets _ _ (fun s _ => setShared_le_left s f₁ f₂)

theorem sharedCompleteness_le_right (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    sharedCompleteness M f₁ f₂ ≤ completeness M f₂ := by
  unfold sharedCompleteness completeness
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact list_sum_map_le M.sets _ _ (fun s _ => setShared_le_right s f₁ f₂)

theorem completeness_zero (M : MarkerFamily α) : completeness M 0 = 0 := by
  unfold completeness setComp
  simp

theorem contamination_zero (M : MarkerFamily α) : contamination M 0 = 0 := by
  unfold contamination setCont
  simp

theorem markerMass_zero (M : MarkerFamily α) : markerMass M 0 = 0 := by
  unfold markerMass setMass
  simp

theorem completeness_mono (M : MarkerFamily α) {f₁ f₂ : α → ℕ} (h : ∀ g, f₁ g ≤ f₂ g) :
    completeness M f₁ ≤ completeness M f₂ := by
  unfold completeness
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact list_sum_map_le M.sets _ _ (fun s _ => setComp_mono s h)

theorem contamination_mono (M : MarkerFamily α) {f₁ f₂ : α → ℕ} (h : ∀ g, f₁ g ≤ f₂ g) :
    contamination M f₁ ≤ contamination M f₂ := by
  unfold contamination
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact list_sum_map_le M.sets _ _ (fun s _ => setCont_mono s h)

/-- **Exact Marker Mass Identity**: For every marker family and profile,
`completeness + contamination = markerMass`. -/
theorem comp_add_cont_eq_mass (M : MarkerFamily α) (f : α → ℕ) :
    completeness M f + contamination M f = markerMass M f := by
  unfold completeness contamination markerMass
  rw [← add_div, ← list_sum_map_add]
  congr 1
  congr 1
  apply List.map_congr_left
  intro s _
  exact setComp_add_setCont s f

/-- **Strict Additivity of Marker Mass**: `markerMass` is an additive valuation on
copy-count profiles. -/
theorem markerMass_add (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    markerMass M (f₁ + f₂) = markerMass M f₁ + markerMass M f₂ := by
  unfold markerMass
  rw [← add_div, ← list_sum_map_add]
  congr 1
  congr 1
  apply List.map_congr_left
  intro s _
  exact setMass_add s f₁ f₂

/-- **Inclusion-Exclusion for Completeness**: Merging two profiles reduces combined
completeness relative to the sum of parts by exactly `sharedCompleteness`. -/
theorem comp_add_eq (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    completeness M (f₁ + f₂) + sharedCompleteness M f₁ f₂ =
      completeness M f₁ + completeness M f₂ := by
  unfold completeness sharedCompleteness
  rw [← add_div, ← add_div, ← list_sum_map_add, ← list_sum_map_add]
  congr 1
  congr 1
  apply List.map_congr_left
  intro s _
  exact setComp_add_setShared s f₁ f₂

/-- **Exact Cross-Contamination Law**: Merging two profiles increases total contamination
by *exactly* their `sharedCompleteness`. -/
theorem cont_add_eq (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    contamination M (f₁ + f₂) =
      contamination M f₁ + contamination M f₂ + sharedCompleteness M f₁ f₂ := by
  unfold contamination sharedCompleteness
  rw [← add_div, ← add_div, ← list_sum_map_add, ← list_sum_map_add]
  congr 1
  congr 1
  apply List.map_congr_left
  intro s _
  exact setCont_add_eq s f₁ f₂

/-- **Conservation Law for Bin Merging and Splitting**: Total marker mass
`completeness + contamination` is strictly conserved across any disjoint merge or split. -/
theorem conservation_law (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    completeness M (f₁ + f₂) + contamination M (f₁ + f₂) =
      (completeness M f₁ + contamination M f₁) + (completeness M f₂ + contamination M f₂) := by
  rw [comp_add_cont_eq_mass, comp_add_cont_eq_mass, comp_add_cont_eq_mass, markerMass_add]

/-- **Multi-way Conservation Law**: For any finite family of disjoint sub-bins `Bs`,
total marker mass is strictly additive. -/
theorem multi_conservation {ι : Type*} [DecidableEq ι]
    (M : MarkerFamily α) (Bs : Finset ι) (f : ι → α → ℕ) :
    completeness M (∑ i ∈ Bs, f i) + contamination M (∑ i ∈ Bs, f i) =
      ∑ i ∈ Bs, (completeness M (f i) + contamination M (f i)) := by
  induction Bs using Finset.induction_on with
  | empty =>
    simp [completeness_zero, contamination_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, conservation_law, ih]

/-- **Subadditivity of Completeness**. -/
theorem comp_subadditive (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    completeness M (f₁ + f₂) ≤ completeness M f₁ + completeness M f₂ := by
  have h1 := comp_add_eq M f₁ f₂
  have h2 := sharedCompleteness_nonneg M f₁ f₂
  linarith

/-- **Superadditivity of Contamination**. -/
theorem cont_superadditive (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    contamination M f₁ + contamination M f₂ ≤ contamination M (f₁ + f₂) := by
  have h1 := cont_add_eq M f₁ f₂
  have h2 := sharedCompleteness_nonneg M f₁ f₂
  linarith

/-- **Split Completeness Ceiling**: Splitting a bin `f₁ + f₂` can recover at most
`completeness + contamination` of the original bin in total completeness. -/
theorem split_completeness_ceiling (M : MarkerFamily α) (f₁ f₂ : α → ℕ) :
    completeness M f₁ + completeness M f₂ ≤
      completeness M (f₁ + f₂) + contamination M (f₁ + f₂) := by
  have hcons := conservation_law M f₁ f₂
  have hc1 := contamination_nonneg M f₁
  have hc2 := contamination_nonneg M f₂
  linarith

/-- **Chimeric Masking Identity**: When a foreign profile `f_contam` is added to a
target `f_target`, the unseen portion of foreign completeness (`comp(f_contam) - shared`)
converts 1-for-1 into artificial completeness inflation. -/
theorem chimeric_masking_identity (M : MarkerFamily α) (f_target f_contam : α → ℕ) :
    completeness M (f_target + f_contam) - completeness M f_target =
      completeness M f_contam - sharedCompleteness M f_target f_contam := by
  have h := comp_add_eq M f_target f_contam
  linarith

/-- For two pure genomes (`contamination = 0`), the contamination observed in their
chimeric merge equals their shared completeness, and is bounded above by the minimum
of their individual completenesses. -/
theorem pure_merge_contamination_eq_shared (M : MarkerFamily α) {f₁ f₂ : α → ℕ}
    (hp₁ : contamination M f₁ = 0) (hp₂ : contamination M f₂ = 0) :
    contamination M (f₁ + f₂) = sharedCompleteness M f₁ f₂ ∧
      contamination M (f₁ + f₂) ≤ min (completeness M f₁) (completeness M f₂) := by
  have hcont : contamination M (f₁ + f₂) = sharedCompleteness M f₁ f₂ := by
    rw [cont_add_eq, hp₁, hp₂]
    ring
  refine ⟨hcont, ?_⟩
  rw [hcont, le_min_iff]
  exact ⟨sharedCompleteness_le_left M f₁ f₂, sharedCompleteness_le_right M f₁ f₂⟩

/-- **Zero-Contamination Partition Characterization**: Two pure profiles merge with
zero observed contamination *if and only if* their shared completeness is zero. -/
theorem pure_merge_zero_cont_iff (M : MarkerFamily α) {f₁ f₂ : α → ℕ}
    (hp₁ : contamination M f₁ = 0) (hp₂ : contamination M f₂ = 0) :
    contamination M (f₁ + f₂) = 0 ↔ sharedCompleteness M f₁ f₂ = 0 := by
  rw [(pure_merge_contamination_eq_shared M hp₁ hp₂).1]

/-- **Constructive Stealth-Chimera Impossibility Theorem**:
For *every* marker family `M` whose total marker set contains at least two distinct
markers, there exist two completely disjoint, pure, nonempty genome profiles `f₁` and `f₂`
whose chimeric merge `f₁ + f₂` achieves `completeness = 1` and `contamination = 0`.
Hence marker-only completeness/contamination can *never* certify purity without
contig-level taxonomic, coverage, or linkage evidence. -/
theorem stealth_chimera_exists (M : MarkerFamily α) (hcard : 2 ≤ M.allMarkers.card) :
    ∃ f₁ f₂ : α → ℕ,
      (∀ g, f₁ g = 0 ∨ f₂ g = 0) ∧
      0 < completeness M f₁ ∧
      0 < completeness M f₂ ∧
      contamination M f₁ = 0 ∧
      contamination M f₂ = 0 ∧
      completeness M (f₁ + f₂) = 1 ∧
      contamination M (f₁ + f₂) = 0 := by
  have h1lt : 1 < M.allMarkers.card := by omega
  rcases Finset.one_lt_card.mp h1lt with ⟨g₁, hg₁, g₂, hg₂, hne⟩
  let f₁ : α → ℕ := fun g => if g = g₁ then 1 else 0
  let f₂ : α → ℕ := fun g => if g = g₁ then 0 else 1
  refine ⟨f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    by_cases h : g = g₁ <;> simp [f₁, f₂, h]
  · -- 0 < completeness M f₁
    rcases MarkerFamily.mem_allMarkers.mp hg₁ with ⟨s₁, hs₁, hg₁s⟩
    unfold completeness
    apply div_pos _ M.numSets_pos_rat
    apply list_sum_map_pos_of_exists M.sets (fun s => setComp s f₁)
      (fun s _ => setComp_nonneg s f₁)
    refine ⟨s₁, hs₁, ?_⟩
    unfold setComp
    apply div_pos _ (M.set_card_pos_rat hs₁)
    have hge : (1 : ℚ) ≤ ∑ g ∈ s₁, (present (f₁ g) : ℚ) := by
      have hmem : (present (f₁ g₁) : ℚ) ≤ ∑ g ∈ s₁, (present (f₁ g) : ℚ) :=
        Finset.single_le_sum (f := fun g => (present (f₁ g) : ℚ)) (fun g _ => by positivity) hg₁s
      simpa [f₁] using hmem
    linarith
  · -- 0 < completeness M f₂
    rcases MarkerFamily.mem_allMarkers.mp hg₂ with ⟨s₂, hs₂, hg₂s⟩
    unfold completeness
    apply div_pos _ M.numSets_pos_rat
    apply list_sum_map_pos_of_exists M.sets (fun s => setComp s f₂)
      (fun s _ => setComp_nonneg s f₂)
    refine ⟨s₂, hs₂, ?_⟩
    unfold setComp
    apply div_pos _ (M.set_card_pos_rat hs₂)
    have hge : (1 : ℚ) ≤ ∑ g ∈ s₂, (present (f₂ g) : ℚ) := by
      have hmem : (present (f₂ g₂) : ℚ) ≤ ∑ g ∈ s₂, (present (f₂ g) : ℚ) :=
        Finset.single_le_sum (f := fun g => (present (f₂ g) : ℚ)) (fun g _ => by positivity) hg₂s
      have hne' : g₂ ≠ g₁ := Ne.symm hne
      simpa [f₂, hne'] using hmem
    linarith
  · -- contamination M f₁ = 0
    unfold contamination setCont
    have hzero : ∀ s ∈ M.sets, (∑ g ∈ s, (excess (f₁ g) : ℚ)) / (s.card : ℚ) = 0 := by
      intro s _
      have : ∀ g ∈ s, (excess (f₁ g) : ℚ) = 0 := by
        intro g _
        by_cases h : g = g₁ <;> simp [f₁, excess, h]
      simp [Finset.sum_eq_zero this]
    have hmap : M.sets.map (fun s => (∑ g ∈ s, (excess (f₁ g) : ℚ)) / (s.card : ℚ)) =
        M.sets.map (fun _ => (0 : ℚ)) :=
      List.map_congr_left hzero
    rw [hmap, list_sum_map_const]
    simp
  · -- contamination M f₂ = 0
    unfold contamination setCont
    have hzero : ∀ s ∈ M.sets, (∑ g ∈ s, (excess (f₂ g) : ℚ)) / (s.card : ℚ) = 0 := by
      intro s _
      have : ∀ g ∈ s, (excess (f₂ g) : ℚ) = 0 := by
        intro g _
        by_cases h : g = g₁ <;> simp [f₂, excess, h]
      simp [Finset.sum_eq_zero this]
    have hmap : M.sets.map (fun s => (∑ g ∈ s, (excess (f₂ g) : ℚ)) / (s.card : ℚ)) =
        M.sets.map (fun _ => (0 : ℚ)) :=
      List.map_congr_left hzero
    rw [hmap, list_sum_map_const]
    simp
  · -- completeness M (f₁ + f₂) = 1
    unfold completeness setComp
    have hone : ∀ s ∈ M.sets, (∑ g ∈ s, (present ((f₁ + f₂) g) : ℚ)) / (s.card : ℚ) = 1 := by
      intro s hs
      have hsum : ∑ g ∈ s, (present ((f₁ + f₂) g) : ℚ) = (s.card : ℚ) := by
        have hpt : ∀ g ∈ s, (present ((f₁ + f₂) g) : ℚ) = 1 := by
          intro g _
          by_cases h : g = g₁ <;> simp [f₁, f₂, Pi.add_apply, h]
        rw [Finset.sum_congr rfl hpt]
        simp
      rw [hsum, div_self (ne_of_gt (M.set_card_pos_rat hs))]
    have hmap : M.sets.map (fun s => (∑ g ∈ s, (present ((f₁ + f₂) g) : ℚ)) / (s.card : ℚ)) =
        M.sets.map (fun _ => (1 : ℚ)) :=
      List.map_congr_left hone
    rw [hmap, list_sum_map_const, mul_one]
    exact div_self (ne_of_gt M.numSets_pos_rat)
  · -- contamination M (f₁ + f₂) = 0
    unfold contamination setCont
    have hzero : ∀ s ∈ M.sets, (∑ g ∈ s, (excess ((f₁ + f₂) g) : ℚ)) / (s.card : ℚ) = 0 := by
      intro s _
      have hpt : ∀ g ∈ s, (excess ((f₁ + f₂) g) : ℚ) = 0 := by
        intro g _
        by_cases h : g = g₁ <;> simp [f₁, f₂, Pi.add_apply, excess, h]
      rw [Finset.sum_eq_zero hpt]
      simp
    have hmap : M.sets.map (fun s => (∑ g ∈ s, (excess ((f₁ + f₂) g) : ℚ)) / (s.card : ℚ)) =
        M.sets.map (fun _ => (0 : ℚ)) :=
      List.map_congr_left hzero
    rw [hmap, list_sum_map_const]
    simp

/-! ### Contig-level lifting & Core-vs-Accessory Invariance -/

/-- Aggregate marker copy counts of a finite bin of contigs. -/
def binCounts {Contig : Type*} [DecidableEq Contig]
    (contigHits : Contig → α → ℕ) (B : Finset Contig) : α → ℕ :=
  fun g => ∑ c ∈ B, contigHits c g

omit [DecidableEq α] in
theorem binCounts_union {Contig : Type*} [DecidableEq Contig]
    (contigHits : Contig → α → ℕ) {B₁ B₂ : Finset Contig} (hdisj : Disjoint B₁ B₂) :
    binCounts contigHits (B₁ ∪ B₂) =
      binCounts contigHits B₁ + binCounts contigHits B₂ := by
  ext g
  simp [binCounts, Pi.add_apply, Finset.sum_union hdisj]

/-- **Core-vs-Accessory Blindness Theorem**: Adding or removing any set of accessory
contigs (plasmids, prophages, mobile islands) that carry no hits to `M.allMarkers`
leaves both `completeness` and `contamination` strictly unchanged. -/
theorem accessory_invariance {Contig : Type*} [DecidableEq Contig]
    (M : MarkerFamily α) (contigHits : Contig → α → ℕ)
    {B A : Finset Contig} (hdisj : Disjoint B A)
    (hacc : ∀ c ∈ A, ∀ g ∈ M.allMarkers, contigHits c g = 0) :
    completeness M (binCounts contigHits (B ∪ A)) = completeness M (binCounts contigHits B) ∧
    contamination M (binCounts contigHits (B ∪ A)) = contamination M (binCounts contigHits B) := by
  have heq_on : ∀ s ∈ M.sets, ∀ g ∈ s,
      binCounts contigHits (B ∪ A) g = binCounts contigHits B g := by
    intro s hs g hg
    rw [binCounts_union contigHits hdisj, Pi.add_apply]
    have hA : binCounts contigHits A g = 0 := by
      unfold binCounts
      apply Finset.sum_eq_zero
      intro c hc
      exact hacc c hc g (MarkerFamily.mem_allMarkers.mpr ⟨s, hs, hg⟩)
    omega
  constructor
  · unfold completeness setComp
    congr 1
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [heq_on s hs g hg]
  · unfold contamination setCont
    congr 1
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [heq_on s hs g hg]

/-! ### Strain Heterogeneity (CheckM-style) -/

/-- Strain heterogeneity: fraction of multi-copy marker pairs whose amino-acid
identity exceeds the strain threshold (e.g. ≥ 90% AAI). Returns `0` when there
are no multi-copy pairs. -/
def strainHeterogeneity (highIdentityPairs totalMultiCopyPairs : ℕ) : ℚ :=
  if totalMultiCopyPairs = 0 then 0
  else (highIdentityPairs : ℚ) / (totalMultiCopyPairs : ℚ)

theorem strainHeterogeneity_nonneg (h t : ℕ) :
    0 ≤ strainHeterogeneity h t := by
  unfold strainHeterogeneity
  split_ifs <;> positivity

theorem strainHeterogeneity_le_one {h t : ℕ} (hle : h ≤ t) :
    strainHeterogeneity h t ≤ 1 := by
  unfold strainHeterogeneity
  split_ifs with ht
  · norm_num
  · have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero ht
    rw [div_le_one htpos]
    exact_mod_cast hle

/-- Non-strain (inter-species) contamination estimate: `cont * (1 - SH)`. -/
def nonStrainContamination (cont sh : ℚ) : ℚ := cont * (1 - sh)

theorem nonStrainContamination_bounds {cont sh : ℚ}
    (hc : 0 ≤ cont) (hsh0 : 0 ≤ sh) (hsh1 : sh ≤ 1) :
    0 ≤ nonStrainContamination cont sh ∧ nonStrainContamination cont sh ≤ cont := by
  unfold nonStrainContamination
  constructor
  · nlinarith
  · nlinarith

end FamilyTheorems

end MAGLean
