module

public import NearCritical.CylinderBK
public import NearCritical.Events
public import Mathlib.MeasureTheory.Measure.Continuity

/-! Infinite-lattice BK from finite-coordinate forcing certificates. The events
need not equal the union of their closed-outside truncations; disjoint occurrence
always does. This distinction includes increasing tail events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

namespace BK

/-- Test A after closing every coordinate outside s. -/
def truncation {E : Type*} (A : Set (E → Bool)) (s : Finset E) : Set (E → Bool) :=
  {ω | Network.certificateConfiguration ω (s : Set E) ∈ A}

lemma certificateConfiguration_le {E : Type*} (s : Finset E) (ω : E → Bool) :
    ConfigLE (Network.certificateConfiguration ω (s : Set E)) ω := by
  intro e he
  by_cases hs : e ∈ s
  · simpa [Network.certificateConfiguration, hs] using he
  · simp [Network.certificateConfiguration, hs] at he

lemma truncation_subset {E : Type*} {A : Set (E → Bool)} (hA : Increasing A)
    (s : Finset E) : truncation A s ⊆ A :=
  fun ω hω ↦ hA (certificateConfiguration_le s ω) hω

lemma truncation_mono {E : Type*} {A : Set (E → Bool)} (hA : Increasing A) :
    Monotone (truncation A) := by
  intro s t hst ω hω
  apply hA ?_ hω
  intro e he
  by_cases hs : e ∈ s
  · have ht := hst hs
    simpa [Network.certificateConfiguration, hs, ht] using he
  · simp [Network.certificateConfiguration, hs] at he

/-- Exhaustion of disjoint occurrence, rather than of the original events.
No countability is needed for this deterministic identity. -/
theorem disjointOccurrence_eq_iUnion_truncation {E : Type*}
    {A B : Set (E → Bool)} (hA : Increasing A) (hB : Increasing B) :
    {ω | DisjointOccurrence A B ω} =
      ⋃ s : Finset E, {ω | DisjointOccurrence (truncation A s) (truncation B s) ω} := by
  ext ω
  constructor
  · rintro ⟨F, H, hFfin, hHfin, hdis, hF, hH⟩
    let s := hFfin.toFinset ∪ hHfin.toFinset
    apply Set.mem_iUnion.mpr
    refine ⟨s, F, H, hFfin, hHfin, hdis, ?_, ?_⟩
    · intro θ hθ
      apply hF
      intro e he
      have hs : e ∈ s := Finset.mem_union.mpr (Or.inl (hFfin.mem_toFinset.mpr he))
      simpa [Network.certificateConfiguration, hs] using hθ e he
    · intro θ hθ
      apply hH
      intro e he
      have hs : e ∈ s := Finset.mem_union.mpr (Or.inr (hHfin.mem_toFinset.mpr he))
      simpa [Network.certificateConfiguration, hs] using hθ e he
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    exact disjointOccurrence_mono (truncation_subset hA s) (truncation_subset hB s) hs

/-- Finite-coordinate version of the closed-outside event. -/
def localTruncation {E : Type*} (A : Set (E → Bool)) (s : Finset E) :
    Set ((e : s) → Bool) :=
  {η | extendConfiguration s (fun _ ↦ false) η ∈ A}

lemma truncation_eq_preimage {E : Type*} (A : Set (E → Bool)) (s : Finset E) :
    truncation A s = s.restrict ⁻¹' localTruncation A s := by
  ext ω
  change (_ ∈ A) ↔ (_ ∈ A)
  have heq : Network.certificateConfiguration ω (s : Set E) =
      extendConfiguration s (fun _ ↦ false) (s.restrict ω) := by
    ext e
    by_cases hs : e ∈ s <;>
      simp [Network.certificateConfiguration, extendConfiguration, hs]
  rw [heq]

lemma increasing_localTruncation {E : Type*} {A : Set (E → Bool)}
    (hA : Increasing A) (s : Finset E) : Increasing (localTruncation A s) := by
  intro η θ hηθ hη
  apply hA ?_ hη
  intro e he
  by_cases hs : e ∈ s
  · simpa [extendConfiguration, hs] using hηθ ⟨e, hs⟩ (by simpa [extendConfiguration, hs] using he)
  · simp [extendConfiguration, hs] at he

end BK

/-- BK for arbitrary increasing events on the countably infinite lattice bond
space, with standard finite forcing disjoint occurrence. Real measures here
are finite outer probabilities, so no measurability premise on A or B is needed. -/
theorem percolation_bk (d : ℕ) (p : unitInterval)
    (A B : Set (Configuration d)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (percolation d p).real {ω | DisjointOccurrence A B ω} ≤
      (percolation d p).real A * (percolation d p).real B := by
  let C := fun s : Finset (Bond d) ↦
    {ω | DisjointOccurrence (BK.truncation A s) (BK.truncation B s) ω}
  have hdir : Directed (· ⊆ ·) C := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact fun ω hω ↦ BK.disjointOccurrence_mono
        (BK.truncation_mono hA (Finset.subset_union_left))
        (BK.truncation_mono hB (Finset.subset_union_left)) hω
    · exact fun ω hω ↦ BK.disjointOccurrence_mono
        (BK.truncation_mono hA (Finset.subset_union_right))
        (BK.truncation_mono hB (Finset.subset_union_right)) hω
  have hb : ∀ s, (percolation d p) (C s) ≤
      ENNReal.ofReal ((percolation d p).real A * (percolation d p).real B) := by
    intro s
    have h := percolation_cylinder_bk d p s (BK.localTruncation A s)
      (BK.localTruncation B s) (BK.increasing_localTruncation hA s)
      (BK.increasing_localTruncation hB s)
    rw [← BK.truncation_eq_preimage, ← BK.truncation_eq_preimage] at h
    have h' := h.trans (mul_le_mul
      (measureReal_mono (BK.truncation_subset hA s))
      (measureReal_mono (BK.truncation_subset hB s)) (measureReal_nonneg) (measureReal_nonneg))
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (mul_nonneg measureReal_nonneg measureReal_nonneg)]
    exact h'
  have hu : (percolation d p) (⋃ s, C s) ≤
      ENNReal.ofReal ((percolation d p).real A * (percolation d p).real B) := by
    rw [hdir.measure_iUnion]
    exact iSup_le hb
  rw [← BK.disjointOccurrence_eq_iUnion_truncation hA hB] at hu
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hu |>.trans
    (le_of_eq (ENNReal.toReal_ofReal (mul_nonneg measureReal_nonneg measureReal_nonneg)))

/-- Despite allowing arbitrary increasing input sets, their finite-forcing
occurrence is measurable, by its countable cylinder exhaustion. -/
theorem measurableSet_disjointOccurrence {d : ℕ}
    {A B : Set (Configuration d)} (hA : BK.Increasing A) (hB : BK.Increasing B) :
    MeasurableSet {ω | DisjointOccurrence A B ω} := by
  rw [BK.disjointOccurrence_eq_iUnion_truncation hA hB]
  apply MeasurableSet.iUnion
  intro s
  rw [BK.truncation_eq_preimage, BK.truncation_eq_preimage]
  have hRestr : Measurable (s.restrict : Configuration d → ((e : s) → Bool)) :=
    Finset.measurable_restrict s
  have hfinite : MeasurableSet (BK.occurrenceEvent
      (BK.localTruncation A s) (BK.localTruncation B s)) := (Set.toFinite _).measurableSet
  have hmeas : MeasurableSet ((s.restrict : Configuration d → ((e : s) → Bool)) ⁻¹' BK.occurrenceEvent
      (BK.localTruncation A s) (BK.localTruncation B s)) := by
    convert! hfinite.preimage hRestr using 1
  convert hmeas using 1
  ext ω
  exact (disjointOccurrence_restrict_iff s _ _ ω).symm

/-- Full-lattice connection events, with no finite-volume restriction. -/
theorem percolation_connection_bk {d : ℕ} (p : unitInterval)
    (x y z w : Vertex d) :
    (percolation d p).real
      {ω | DisjointOccurrence (connectionEvent x y) (connectionEvent z w) ω} ≤
      (percolation d p).real (connectionEvent x y) *
      (percolation d p).real (connectionEvent z w) := by
  apply percolation_bk
  · exact fun _ _ h hxy ↦ SimpleGraph.Reachable.mono (openGraph_mono h) hxy
  · exact fun _ _ h hzw ↦ SimpleGraph.Reachable.mono (openGraph_mono h) hzw

/-- Infinite-cluster events are admissible increasing events too. Their standard
finite-forcing occurrence may be empty; no infinite certificate is substituted. -/
theorem percolation_infiniteCluster_bk (d : ℕ) (p : unitInterval)
    (A : Set (Configuration d)) (hA : BK.Increasing A) :
    (percolation d p).real
      {ω | DisjointOccurrence A (infiniteClusterEvent d) ω} ≤
      (percolation d p).real A * (percolation d p).real (infiniteClusterEvent d) := by
  apply percolation_bk d p A (infiniteClusterEvent d) hA
  intro ω η h hω
  exact hω.mono (cluster_mono h 0)

end NearCritical
