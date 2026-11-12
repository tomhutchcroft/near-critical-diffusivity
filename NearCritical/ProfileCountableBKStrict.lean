module

public import NearCritical.ProfileBKStrict
public import NearCritical.CountableBK

/-! Actual infinite-profile BK with a uniform rate bound P<1.
The deterministic finite-forcing exhaustion is reused unchanged; the input
events themselves need not be exhausted by their closed-outside truncations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory
open scoped Classical

lemma profileEventProbability_cylinder (d : ℕ) (r : Bond d → unitInterval)
    (s : Finset (Bond d)) (A : Set ((e : s) → Bool)) :
    BK.profileEventProbability (fun e : s ↦ (r e.val : ℝ)) A =
      (percolationProfile d r).real ((s.restrict) ⁻¹' A) := by
  calc
    _ = ∫ ω, (if s.restrict ω ∈ A then (1 : ℝ) else 0) ∂percolationProfile d r :=
      (percolationProfile_cylinder_expectation d r s
        (fun η ↦ if η ∈ A then (1 : ℝ) else 0)).symm
    _ = _ := by
      have hA : MeasurableSet A := (Set.toFinite A).measurableSet
      have hRestr : Measurable (s.restrict : Configuration d → ((e : s) → Bool)) :=
        Finset.measurable_restrict s
      have hs : MeasurableSet {ω : Configuration d | s.restrict ω ∈ A} := by
        convert! hA.preimage hRestr using 1
      convert! integral_indicator_one (μ := percolationProfile d r) hs using 1

/-- Cylinder BK retains both original profile factors. -/
theorem percolationProfile_cylinder_bk_of_uniform_lt_one (d : ℕ)
    (r : Bond d → unitInterval) (P : unitInterval) (hP : (P : ℝ) < 1)
    (hr : ∀ e, r e ≤ P) (s : Finset (Bond d))
    (A B : Set ((e : s) → Bool)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (percolationProfile d r).real
        {ω | DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω} ≤
      (percolationProfile d r).real ((s.restrict) ⁻¹' A) *
        (percolationProfile d r).real ((s.restrict) ⁻¹' B) := by
  have heq : {ω | DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω} =
      (s.restrict) ⁻¹' BK.occurrenceEvent A B := by
    ext ω
    exact (disjointOccurrence_restrict_iff s A B ω).symm
  rw [heq]
  have h := BK.finite_bernoulliProfile_bk_of_uniform_lt_one
    (fun e : s ↦ r e.val) P hP (fun e ↦ hr e.val) A B hA hB
  rw [← BK.profileEventProbability_eq_measureReal,
    ← BK.profileEventProbability_eq_measureReal,
    ← BK.profileEventProbability_eq_measureReal] at h
  rw [profileEventProbability_cylinder d r s, profileEventProbability_cylinder d r s,
    profileEventProbability_cylinder d r s] at h
  exact h

/-- Countable finite-forcing BK under the actual independent profile law.
The common P<1 hypothesis is explicit; no endpoint-one extension is claimed. -/
theorem percolationProfile_bk_of_uniform_lt_one (d : ℕ) (r : Bond d → unitInterval)
    (P : unitInterval) (hP : (P : ℝ) < 1) (hr : ∀ e, r e ≤ P)
    (A B : Set (Configuration d)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (percolationProfile d r).real {ω | DisjointOccurrence A B ω} ≤
      (percolationProfile d r).real A * (percolationProfile d r).real B := by
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
  have hb : ∀ s, (percolationProfile d r) (C s) ≤
      ENNReal.ofReal ((percolationProfile d r).real A * (percolationProfile d r).real B) := by
    intro s
    have h := percolationProfile_cylinder_bk_of_uniform_lt_one d r P hP hr s (BK.localTruncation A s)
      (BK.localTruncation B s) (BK.increasing_localTruncation hA s)
      (BK.increasing_localTruncation hB s)
    rw [← BK.truncation_eq_preimage, ← BK.truncation_eq_preimage] at h
    have h' := h.trans (mul_le_mul
      (measureReal_mono (BK.truncation_subset hA s))
      (measureReal_mono (BK.truncation_subset hB s)) (measureReal_nonneg) (measureReal_nonneg))
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (mul_nonneg measureReal_nonneg measureReal_nonneg)]
    exact h'
  have hu : (percolationProfile d r) (⋃ s, C s) ≤
      ENNReal.ofReal ((percolationProfile d r).real A * (percolationProfile d r).real B) := by
    rw [hdir.measure_iUnion]
    exact iSup_le hb
  rw [← BK.disjointOccurrence_eq_iUnion_truncation hA hB] at hu
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hu |>.trans
    (le_of_eq (ENNReal.toReal_ofReal (mul_nonneg measureReal_nonneg measureReal_nonneg)))

end NearCritical
