import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# MAGLean.Basic

Core biological and combinatorial structures for formalizing Metagenome-Assembled
Genomes (MAGs): markers, collocated marker families (CheckM-style), contigs, bins,
and taxonomic ranks.
-/

namespace MAGLean

/-- Standard seven taxonomic ranks used in GTDB / NCBI / GUNC, ordered from
broadest (`domain`) to most specific (`species`). -/
inductive TaxRank : Type where
  | domain
  | phylum
  | class_
  | order
  | family
  | genus
  | species
  deriving DecidableEq, Repr, Inhabited

namespace TaxRank

/-- Numeric depth of a taxonomic rank (`0` = domain, `6` = species). -/
def toNat : TaxRank → ℕ
  | domain  => 0
  | phylum  => 1
  | class_  => 2
  | order   => 3
  | family  => 4
  | genus   => 5
  | species => 6

/-- All seven ranks in ascending order of specificity. -/
def all : List TaxRank :=
  [domain, phylum, class_, order, family, genus, species]

/-- Human-readable label for a rank. -/
def label : TaxRank → String
  | domain  => "domain"
  | phylum  => "phylum"
  | class_  => "class"
  | order   => "order"
  | family  => "family"
  | genus   => "genus"
  | species => "species"

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> simp [toNat] at h <;> rfl

instance : LinearOrder TaxRank :=
  LinearOrder.lift' toNat toNat_injective

theorem le_iff_toNat_le (a b : TaxRank) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

theorem lt_iff_toNat_lt (a b : TaxRank) : a < b ↔ a.toNat < b.toNat := Iff.rfl

end TaxRank

/-- A collocated single-copy marker family (CheckM model): a nonempty list of
nonempty finite sets of markers, where co-located genes (e.g. operons) are grouped
into a single marker set so physical linkage does not over-weight a locus. -/
structure MarkerFamily (α : Type*) [DecidableEq α] where
  sets : List (Finset α)
  sets_nonempty : sets ≠ []
  mem_nonempty : ∀ s ∈ sets, s.Nonempty

namespace MarkerFamily

variable {α : Type*} [DecidableEq α]

/-- Number of collocated marker sets in the family (`k ≥ 1`). -/
def numSets (M : MarkerFamily α) : ℕ := M.sets.length

theorem numSets_pos (M : MarkerFamily α) : 0 < M.numSets :=
  List.length_pos_of_ne_nil M.sets_nonempty

theorem numSets_pos_rat (M : MarkerFamily α) : (0 : ℚ) < (M.numSets : ℚ) := by
  exact_mod_cast M.numSets_pos

theorem set_card_pos (M : MarkerFamily α) {s : Finset α} (hs : s ∈ M.sets) :
    0 < s.card :=
  (M.mem_nonempty s hs).card_pos

theorem set_card_pos_rat (M : MarkerFamily α) {s : Finset α} (hs : s ∈ M.sets) :
    (0 : ℚ) < (s.card : ℚ) := by
  exact_mod_cast M.set_card_pos hs

/-- Union of all markers appearing anywhere in the family. -/
def allMarkers (M : MarkerFamily α) : Finset α :=
  M.sets.foldr (· ∪ ·) ∅

theorem mem_allMarkers {M : MarkerFamily α} {g : α} :
    g ∈ M.allMarkers ↔ ∃ s ∈ M.sets, g ∈ s := by
  unfold allMarkers
  induction M.sets with
  | nil => simp
  | cons s rest ih =>
    simp [List.foldr, ih]

/-- Build a singleton-set marker family where every marker is treated as independent
(i.e. each collocated set has size 1). -/
def ofSingletons (markers : List α) (hne : markers ≠ []) : MarkerFamily α where
  sets := markers.map (fun g => ({g} : Finset α))
  sets_nonempty := by simp [hne]
  mem_nonempty := by
    intro s hs
    rcases List.mem_map.mp hs with ⟨g, _, rfl⟩
    exact Finset.singleton_nonempty g

end MarkerFamily

/-- Indicator for marker presence (`1` if present at least once, `0` otherwise). -/
def present (n : ℕ) : ℕ := if n = 0 then 0 else 1

/-- Excess copy count above 1 (`max(0, n - 1)`), using truncated `ℕ` subtraction. -/
def excess (n : ℕ) : ℕ := n - 1

/-- Indicator that a marker is present in *both* profiles `a` and `b`. -/
def shared (a b : ℕ) : ℕ := if a > 0 ∧ b > 0 then 1 else 0

@[simp] theorem present_zero : present 0 = 0 := rfl
@[simp] theorem present_succ (n : ℕ) : present (n + 1) = 1 := rfl
@[simp] theorem excess_zero : excess 0 = 0 := rfl
@[simp] theorem excess_succ (n : ℕ) : excess (n + 1) = n := rfl

theorem present_le_one (n : ℕ) : present n ≤ 1 := by
  cases n <;> simp [present]

theorem present_mono {a b : ℕ} (h : a ≤ b) : present a ≤ present b := by
  unfold present
  split_ifs <;> omega

theorem excess_mono {a b : ℕ} (h : a ≤ b) : excess a ≤ excess b := by
  unfold excess
  omega

/-- Fundamental pointwise conservation law: presence + excess = raw copy count. -/
theorem present_add_excess (n : ℕ) : present n + excess n = n := by
  cases n with
  | zero => rfl
  | succ k => simp [present, excess]; omega

/-- Pointwise inclusion-exclusion for marker presence under bin merging. -/
theorem present_add_shared (a b : ℕ) :
    present (a + b) + shared a b = present a + present b := by
  unfold present shared
  split_ifs <;> omega

/-- Pointwise exact cross-contamination law under bin merging. -/
theorem excess_add_eq (a b : ℕ) :
    excess (a + b) = excess a + excess b + shared a b := by
  unfold excess shared
  split_ifs <;> omega

theorem shared_le_present_left (a b : ℕ) : shared a b ≤ present a := by
  unfold shared present
  split_ifs <;> omega

theorem shared_le_present_right (a b : ℕ) : shared a b ≤ present b := by
  unfold shared present
  split_ifs <;> omega

theorem shared_comm (a b : ℕ) : shared a b = shared b a := by
  unfold shared
  split_ifs <;> omega

theorem shared_eq_zero_iff (a b : ℕ) : shared a b = 0 ↔ a = 0 ∨ b = 0 := by
  unfold shared
  split_ifs with h
  · simp; omega
  · simp; omega

end MAGLean
