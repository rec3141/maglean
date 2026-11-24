import MAGLean.Taxonomy
import MAGLean.Quality

/-!
# MAGLean.Binning

Formal invariants of metagenome binning partitions, global assembly-wide conservation
of base pairs and marker mass, and a verified QC-gated bin-selection operator.

## Main Results

* `binOf_disjoint`: Every binning assigns each contig to at most one bin (zero duplication).
* `assembly_length_conservation`: Sum of binned lengths + unbinned length equals total
  assembly length identically.
* `global_metagenome_marker_conservation`: Across *any* binning of a metagenome assembly `A`
  into bins `B₁, ..., Bₘ` plus unbinned contigs `U`,
  `∑ b, (Comp(B_b) + Cont(B_b)) + (Comp(U) + Cont(U)) = Comp(A) + Cont(A)`.
  No binner can create or destroy single-copy marker mass!
* `filterValidBins_sound`: A verified QC-filtering operator (gating on completeness,
  contamination, and taxonomic purity) preserves binning validity and guarantees every
  retained bin meets all declared thresholds.
-/

namespace MAGLean.Binning

open MAGLean.Taxonomy

section PartitionInvariants

variable {Contig BinId Marker Taxon : Type*}
  [DecidableEq Contig] [DecidableEq BinId] [DecidableEq Marker] [DecidableEq Taxon]

/-- A strict binning of contigs into optional bin IDs (`none` = unbinned). -/
abbrev BinMap (Contig BinId : Type*) := Contig → Option BinId

/-- Contigs in assembly `A` assigned to bin `b`. -/
def binOf (A : Finset Contig) (β : BinMap Contig BinId) (b : BinId) : Finset Contig :=
  A.filter (fun c => β c = some b)

/-- Contigs in assembly `A` left unbinned. -/
def unbinned (A : Finset Contig) (β : BinMap Contig BinId) : Finset Contig :=
  A.filter (fun c => β c = none)

/-- All bin IDs receiving at least one contig from `A`. -/
def activeBins (A : Finset Contig) (β : BinMap Contig BinId) : Finset BinId :=
  A.biUnion (fun c => (β c).toFinset)

omit [DecidableEq Contig] in
/-- **Zero-Duplication Invariant**: Distinct bins never share a contig. -/
theorem binOf_disjoint (A : Finset Contig) (β : BinMap Contig BinId)
    {b₁ b₂ : BinId} (hne : b₁ ≠ b₂) :
    Disjoint (binOf A β b₁) (binOf A β b₂) := by
  rw [Finset.disjoint_left]
  intro c hc1 hc2
  simp only [binOf, Finset.mem_filter] at hc1 hc2
  rw [hc1.2] at hc2
  injection hc2.2 with h
  exact hne h

omit [DecidableEq Contig] in
/-- Binned contigs are strictly disjoint from unbinned contigs. -/
theorem binOf_disjoint_unbinned (A : Finset Contig) (β : BinMap Contig BinId) (b : BinId) :
    Disjoint (binOf A β b) (unbinned A β) := by
  rw [Finset.disjoint_left]
  intro c hc1 hc2
  simp only [binOf, unbinned, Finset.mem_filter] at hc1 hc2
  rw [hc1.2] at hc2
  exact Option.some_ne_none b hc2.2

/-- Exact partition of assembly `A` into active bins plus unbinned contigs. -/
theorem assembly_partition_eq (A : Finset Contig) (β : BinMap Contig BinId) :
    (activeBins A β).biUnion (binOf A β) ∪ unbinned A β = A := by
  ext c
  simp only [Finset.mem_union, Finset.mem_biUnion, activeBins, binOf, unbinned, Finset.mem_filter]
  constructor
  · rintro (⟨b, _, hc, _⟩ | ⟨hc, _⟩) <;> exact hc
  · intro hc
    cases h : β c with
    | none => right; exact ⟨hc, rfl⟩
    | some b =>
      left
      exact ⟨b, ⟨c, hc, by simp [h]⟩, hc, rfl⟩

/-- Helper: additive aggregation over an assembly equals the sum over active bins
plus the unbinned fraction. -/
theorem sum_over_binning {R : Type*} [AddCommMonoid R]
    (A : Finset Contig) (β : BinMap Contig BinId) (w : Contig → R) :
    (∑ b ∈ activeBins A β, ∑ c ∈ binOf A β b, w c) + ∑ c ∈ unbinned A β, w c =
      ∑ c ∈ A, w c := by
  have hpw : Set.PairwiseDisjoint (↑(activeBins A β) : Set BinId) (binOf A β) := by
    intro b₁ _ b₂ _ hne
    exact binOf_disjoint A β hne
  have hdisj : Disjoint ((activeBins A β).biUnion (binOf A β)) (unbinned A β) := by
    rw [Finset.disjoint_biUnion_left]
    intro b _
    exact binOf_disjoint_unbinned A β b
  rw [← Finset.sum_biUnion hpw, ← Finset.sum_union hdisj, assembly_partition_eq]

/-- **Assembly Base-Pair Conservation Law**: Total binned bp + unbinned bp = assembly bp. -/
theorem assembly_length_conservation (A : Finset Contig) (β : BinMap Contig BinId)
    (len : Contig → ℕ) :
    (∑ b ∈ activeBins A β, totalLen (binOf A β b) len) + totalLen (unbinned A β) len =
      totalLen A len := by
  unfold totalLen
  exact sum_over_binning A β (fun c => (len c : ℚ))

/-- **Global Metagenome Marker-Mass Conservation Law**:
Across *any* binning of a metagenome assembly `A` into bins `B_b` plus unbinned contigs `U`,
the sum of `completeness + contamination` over all bins and unbinned contigs equals
`completeness(A) + contamination(A)` identically. No binner can create or destroy
single-copy marker mass! -/
theorem global_metagenome_marker_conservation
    (M : MarkerFamily Marker) (A : Finset Contig) (β : BinMap Contig BinId)
    (hits : Contig → Marker → ℕ) :
    (∑ b ∈ activeBins A β,
        (completeness M (binCounts hits (binOf A β b)) +
          contamination M (binCounts hits (binOf A β b)))) +
      (completeness M (binCounts hits (unbinned A β)) +
        contamination M (binCounts hits (unbinned A β))) =
      completeness M (binCounts hits A) + contamination M (binCounts hits A) := by
  have hagg :
      (∑ b ∈ activeBins A β, binCounts hits (binOf A β b)) + binCounts hits (unbinned A β) =
        binCounts hits A := by
    ext g
    simp only [Pi.add_apply, Finset.sum_apply, binCounts]
    exact sum_over_binning A β (fun c => hits c g)
  rw [← hagg, conservation_law, multi_conservation]

/-! ### Verified QC-Gated Bin Selection Operator -/

/-- Acceptance criteria for retaining a bin after QC filtering. -/
structure BinQCGate where
  minComp : ℚ
  maxCont : ℚ
  minPurity : ℚ
  checkRank : TaxRank

/-- Decidable predicate certifying whether bin `B` passes a `BinQCGate`. -/
def passesGate (M : MarkerFamily Marker) (hits : Contig → Marker → ℕ)
    (len : Contig → ℕ) (τ : Contig → TaxRank → Option Taxon)
    (gate : BinQCGate) (B : Finset Contig) : Bool :=
  decide (gate.minComp ≤ completeness M (binCounts hits B) ∧
          contamination M (binCounts hits B) ≤ gate.maxCont ∧
          gate.minPurity ≤ purityCons B len τ gate.checkRank)

/-- Verified QC-gated bin selector: retains a contig's bin assignment iff its bin
passes `gate`, otherwise releases the contig to `unbinned` (`none`). -/
def filterValidBins (A : Finset Contig) (β : BinMap Contig BinId)
    (M : MarkerFamily Marker) (hits : Contig → Marker → ℕ)
    (len : Contig → ℕ) (τ : Contig → TaxRank → Option Taxon)
    (gate : BinQCGate) : BinMap Contig BinId :=
  fun c =>
    match β c with
    | none => none
    | some b =>
      if passesGate M hits len τ gate (binOf A β b) then some b else none

lemma binOf_filterValidBins_of_pass (A : Finset Contig) (β : BinMap Contig BinId)
    (M : MarkerFamily Marker) (hits : Contig → Marker → ℕ)
    (len : Contig → ℕ) (τ : Contig → TaxRank → Option Taxon)
    (gate : BinQCGate) {b : BinId}
    (hpass : passesGate M hits len τ gate (binOf A β b) = true) :
    binOf A (filterValidBins A β M hits len τ gate) b = binOf A β b := by
  ext c
  simp only [binOf, Finset.mem_filter]
  constructor
  · rintro ⟨hc, hβ'⟩
    dsimp only [filterValidBins] at hβ'
    cases h : β c with
    | none => simp [h] at hβ'
    | some b' =>
      rw [h] at hβ'
      dsimp only at hβ'
      split_ifs at hβ' with hp
      · injection hβ' with hb; subst hb; exact ⟨hc, rfl⟩
  · rintro ⟨hc, hβ⟩
    refine ⟨hc, ?_⟩
    dsimp only [filterValidBins]
    rw [hβ]
    simp [hpass]

/-- **Soundness of Verified QC-Gated Bin Selection**:
Every active bin produced by `filterValidBins` is guaranteed to satisfy the declared
minimum completeness, maximum contamination, and minimum taxonomic purity thresholds,
while preserving strict contig disjointness and global base-pair / marker-mass conservation. -/
theorem filterValidBins_sound (A : Finset Contig) (β : BinMap Contig BinId)
    (M : MarkerFamily Marker) (hits : Contig → Marker → ℕ)
    (len : Contig → ℕ) (τ : Contig → TaxRank → Option Taxon)
    (gate : BinQCGate) :
    let β' := filterValidBins A β M hits len τ gate
    ∀ b ∈ activeBins A β',
      gate.minComp ≤ completeness M (binCounts hits (binOf A β' b)) ∧
      contamination M (binCounts hits (binOf A β' b)) ≤ gate.maxCont ∧
      gate.minPurity ≤ purityCons (binOf A β' b) len τ gate.checkRank := by
  intro β' b hb
  rcases Finset.mem_biUnion.mp hb with ⟨c, _, hcb⟩
  have hβ'c : β' c = some b := by simpa using hcb
  dsimp only [β', filterValidBins] at hβ'c
  cases h : β c with
  | none => simp [h] at hβ'c
  | some b₀ =>
    rw [h] at hβ'c
    dsimp only at hβ'c
    split_ifs at hβ'c with hpass
    · injection hβ'c with hb0
      subst hb0
      have hbin_eq : binOf A β' b₀ = binOf A β b₀ :=
        binOf_filterValidBins_of_pass A β M hits len τ gate hpass
      rw [hbin_eq]
      exact of_decide_eq_true hpass

end PartitionInvariants

end MAGLean.Binning
