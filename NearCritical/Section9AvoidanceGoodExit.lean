module
public import NearCritical.Section9AvoidanceOccurrence
public import NearCritical.FiniteReimerInput

/-! Good last-exit candidates retain the original no-hit guard on the inner
endpoint, without changing the actual suffix avoidance event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The original avoidance event can use only exits whose inner endpoint is
outside the forbidden target. -/
def section9AvoidanceGoodLastExitCandidates {d : ℕ}
    (D C Q F V : Finset (Vertex d)) : Finset ((Vertex d × Vertex d) × Bond d) :=
  (section9AvoidanceLastExitCandidates D C Q F).filter fun t => t.1.1 ∉ V

/-- Original avoidance is covered by good-index nested occurrences. The
prefix still lives in D; original nonhit concerns the SAME larger T. -/
theorem section9_avoidance_subset_good_last_exit_occurrence_union {d : ℕ}
    (D T C Q F B V : Finset (Vertex d)) {z : Vertex d}
    (hzD : z ∈ D) (hzC : z ∈ C) (hDT : D ⊆ T) (hBC : Disjoint B C) :
    section9AvoidanceEvent D T Q F B V z ⊆
      ⋃ t ∈ section9AvoidanceGoodLastExitCandidates D C Q F V,
        section9AvoidanceLastExitOccurrence D T C Q F B V z t := by
  intro ω hω
  have hcover := section9_avoidance_subset_last_exit_occurrence_union D T C Q F B V
    hzD hzC hDT hBC hω
  obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hcover
  obtain ⟨htJ,hocc⟩ := Set.mem_iUnion.mp ht
  have hprefix : t.1.1 ∈ sprinklingUnexploredCluster ω D Q F z := by
    change DisjointOccurrence
      {θ | t.1.1 ∈ sprinklingUnexploredCluster θ D Q F z}
      {θ | DisjointOccurrence {η | η t.2 = true}
        (section9AvoidanceEvent (D \ C) T Q F B V t.1.2) θ} ω at hocc
    exact (BK.disjointOccurrence_mem hocc).1
  have huNot : t.1.1 ∉ V := by
    intro huV
    obtain ⟨huD,hreach⟩ := (mem_sprinklingUnexploredCluster ω D Q F z t.1.1).mp hprefix
    have hle : sprinklingUnexploredGraph ω D Q F ≤ sprinklingUnexploredGraph ω T Q F :=
      fun _ _ h => ⟨h.1,hDT h.2.1,hDT h.2.2.1,h.2.2.2⟩
    apply hω.2
    exact ⟨t.1.1,Finset.mem_inter.mpr
      ⟨(mem_sprinklingUnexploredCluster ω T Q F z t.1.1).mpr
        ⟨hDT huD,hreach.mono hle⟩,huV⟩⟩
  exact Set.mem_iUnion.mpr ⟨t,Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨htJ,huNot⟩,hocc⟩⟩

private theorem avoidance_disjointOccurrence_locality {d : ℕ}
    (s : Finset (Bond d)) (A B : Set (Configuration d))
    (hA : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ A ↔ θ ∈ A))
    (hB : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ B ↔ θ ∈ B)) :
    ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) →
      (DisjointOccurrence A B ω ↔ DisjointOccurrence A B θ) := by
  let A₀ : Set ((b : s) → Bool) := {η | extendConfiguration s (fun _ => false) η ∈ A}
  let B₀ : Set ((b : s) → Bool) := {η | extendConfiguration s (fun _ => false) η ∈ B}
  have hAe : A = (s.restrict) ⁻¹' A₀ := by
    ext ω
    apply hA ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  have hBe : B = (s.restrict) ⁻¹' B₀ := by
    ext ω
    apply hB ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  intro ω θ hagree
  have heq : s.restrict ω = s.restrict θ := by
    funext b
    exact hagree b b.property
  rw [hAe,hBe,← disjointOccurrence_restrict_iff s A₀ B₀ ω,
    ← disjointOccurrence_restrict_iff s A₀ B₀ θ,heq]

private theorem avoidance_event_locality {d : ℕ}
    (D T Q F B V : Finset (Vertex d)) (root : Vertex d) (s : Finset (Bond d))
    (hD : sprinklingAvailableBonds D Q F ⊆ s)
    (hT : sprinklingAvailableBonds T Q F ⊆ s) :
    ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) →
      (ω ∈ section9AvoidanceEvent D T Q F B V root ↔
       θ ∈ section9AvoidanceEvent D T Q F B V root) := by
  intro ω θ hagree
  have h₁ := sprinklingUnexploredCluster_eq_of_available_agree D Q F ω θ
    (fun b hb => hagree b (hD hb)) root
  have h₂ := sprinklingUnexploredCluster_eq_of_available_agree T Q F ω θ
    (fun b hb => hagree b (hT hb)) root
  simp only [section9AvoidanceEvent,Set.mem_setOf_eq,h₁,h₂]

/-- Every individual actual nested last-exit occurrence obeys the finite
BKR product bound. No candidate membership or geometric premise is required. -/
theorem section9_avoidance_last_exit_occurrence_probability_le {d : ℕ}
    (reimer : FiniteBernoulliBKRInput) (p : unitInterval)
    (D T C Q F B V : Finset (Vertex d)) (z : Vertex d)
    (t : (Vertex d × Vertex d) × Bond d) :
    (percolation d p).real (section9AvoidanceLastExitOccurrence D T C Q F B V z t) ≤
      (p : ℝ)*(percolation d p).real
        {θ | t.1.1 ∈ sprinklingUnexploredCluster θ D Q F z} *
      (percolation d p).real (section9AvoidanceEvent (D \ C) T Q F B V t.1.2) := by
  let A : Set (Configuration d) := {θ | t.1.1 ∈ sprinklingUnexploredCluster θ D Q F z}
  let O : Set (Configuration d) := {θ | θ t.2 = true}
  let H := section9AvoidanceEvent (D \ C) T Q F B V t.1.2
  let s : Finset (Bond d) :=
    ((sprinklingAvailableBonds D Q F ∪ sprinklingAvailableBonds (D \ C) Q F) ∪
      sprinklingAvailableBonds T Q F) ∪ {t.2}
  have hDs : sprinklingAvailableBonds D Q F ⊆ s := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hb)))))
  have hDCs : sprinklingAvailableBonds (D \ C) Q F ⊆ s := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inr hb)))))
  have hTs : sprinklingAvailableBonds T Q F ⊆ s := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hb)))
  have hbs : t.2 ∈ s := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
  have hA : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ A ↔ θ ∈ A) := by
    intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree D Q F ω θ
      (fun b hb => hagree b (hDs hb)) z
    simp only [A,Set.mem_setOf_eq,heq]
  have hO : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ O ↔ θ ∈ O) := by
    intro ω θ hagree
    simp only [O,Set.mem_setOf_eq,hagree t.2 hbs]
  have hH : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ H ↔ θ ∈ H) :=
    avoidance_event_locality (D \ C) T Q F B V t.1.2 s hDCs hTs
  have hOH := avoidance_disjointOccurrence_locality s O H hO hH
  have hOuter := percolation_reimer_of_finite_locality reimer d p s A
    {θ | DisjointOccurrence O H θ} hA hOH
  have hInner := percolation_reimer_of_finite_locality reimer d p s O H hO hH
  have hMarginal : (percolation d p).real O = (p : ℝ) := by
    change (percolation d p).real {θ | θ t.2 = true} = (p : ℝ)
    rw [measureReal_def,percolation_open_bond,ENNReal.toReal_ofReal p.property.1]
  calc
    _ ≤ (percolation d p).real A *
        (percolation d p).real {θ | DisjointOccurrence O H θ} := hOuter
    _ ≤ (percolation d p).real A *
        ((percolation d p).real O*(percolation d p).real H) :=
      mul_le_mul_of_nonneg_left hInner measureReal_nonneg
    _ = _ := by rw [hMarginal]; ring

/-- The actual ordinary fresh avoidance upper bound retains good exits,
with exactly the original suffix event and full nonhit tube. -/
theorem section9_avoidance_probability_le_good_candidate_products {d : ℕ}
    (reimer : FiniteBernoulliBKRInput) (p : unitInterval)
    (D T C Q F B V : Finset (Vertex d)) {z : Vertex d}
    (hzD : z ∈ D) (hzC : z ∈ C) (hDT : D ⊆ T) (hBC : Disjoint B C) :
    (percolation d p).real (section9AvoidanceEvent D T Q F B V z) ≤
      ∑ t ∈ section9AvoidanceGoodLastExitCandidates D C Q F V,
        (p : ℝ)*(percolation d p).real
          {θ | t.1.1 ∈ sprinklingUnexploredCluster θ D Q F z} *
        (percolation d p).real (section9AvoidanceEvent (D \ C) T Q F B V t.1.2) := by
  calc
    _ ≤ (percolation d p).real
        (⋃ t ∈ section9AvoidanceGoodLastExitCandidates D C Q F V,
          section9AvoidanceLastExitOccurrence D T C Q F B V z t) :=
      measureReal_mono
        (section9_avoidance_subset_good_last_exit_occurrence_union D T C Q F B V hzD hzC hDT hBC)
        (measure_ne_top _ _)
    _ ≤ ∑ t ∈ section9AvoidanceGoodLastExitCandidates D C Q F V,
        (percolation d p).real (section9AvoidanceLastExitOccurrence D T C Q F B V z t) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun t _ =>
      section9_avoidance_last_exit_occurrence_probability_le reimer p D T C Q F B V z t

end NearCritical
