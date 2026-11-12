module

public import NearCritical.Harris
public import NearCritical.CountableBK
public import NearCritical.ChemicalConnection

/-! Positive association for increasing events exhausted by finite open witnesses,
and genuine full-lattice escape events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

lemma percolation_truncation_harris (d : ℕ) (p : unitInterval)
    {A B : Set (Configuration d)} (hA : BK.Increasing A) (hB : BK.Increasing B)
    (s : Finset (Bond d)) :
    percolation d p (BK.truncation A s) * percolation d p (BK.truncation B s) ≤
      percolation d p (BK.truncation A s ∩ BK.truncation B s) := by
  have h := percolation_cylinder_harris d p s (BK.localTruncation A s)
    (BK.localTruncation B s) (BK.increasing_localTruncation hA s)
    (BK.increasing_localTruncation hB s)
  rw [← BK.truncation_eq_preimage, ← BK.truncation_eq_preimage] at h
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) (measure_ne_top _ _)).mp
  simpa only [ENNReal.toReal_mul, Measure.real] using h

/-- Positive association for events with a proved finite-witness exhaustion.
This hypothesis is not asserted for arbitrary increasing tail events. -/
theorem percolation_harris_of_finite_witnesses (d : ℕ) (p : unitInterval)
    {A B : Set (Configuration d)} (hA : BK.Increasing A) (hB : BK.Increasing B)
    (hAe : A = ⋃ s : Finset (Bond d), BK.truncation A s)
    (hBe : B = ⋃ s : Finset (Bond d), BK.truncation B s) :
    percolation d p A * percolation d p B ≤ percolation d p (A ∩ B) := by
  have hμA : percolation d p A = ⨆ s, percolation d p (BK.truncation A s) := by
    calc
      _ = percolation d p (⋃ s : Finset (Bond d), BK.truncation A s) := congrArg _ hAe
      _ = _ := (BK.truncation_mono hA).directed_le.measure_iUnion
  have hμB : percolation d p B = ⨆ s, percolation d p (BK.truncation B s) := by
    calc
      _ = percolation d p (⋃ s : Finset (Bond d), BK.truncation B s) := congrArg _ hBe
      _ = _ := (BK.truncation_mono hB).directed_le.measure_iUnion
  rw [hμA, hμB, ENNReal.iSup_mul]
  apply iSup_le
  intro s
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro t
  calc
    _ ≤ percolation d p (BK.truncation A (s ∪ t)) *
        percolation d p (BK.truncation B (s ∪ t)) :=
      mul_le_mul' (measure_mono (BK.truncation_mono hA Finset.subset_union_left))
        (measure_mono (BK.truncation_mono hB Finset.subset_union_right))
    _ ≤ percolation d p (BK.truncation A (s ∪ t) ∩ BK.truncation B (s ∪ t)) :=
      percolation_truncation_harris d p hA hB (s ∪ t)
    _ ≤ _ := measure_mono (inter_subset_inter
      (BK.truncation_subset hA _) (BK.truncation_subset hB _))

/-- A full-lattice open path from x to outside a finite set of vertices. -/
def escapeEvent {d : ℕ} (x : Vertex d) (s : Finset (Vertex d)) : Set (Configuration d) :=
  {ω | ∃ y, y ∉ s ∧ (openGraph ω).Reachable x y}

lemma measurableSet_escapeEvent {d : ℕ} (x : Vertex d) (s : Finset (Vertex d)) :
    MeasurableSet (escapeEvent x s) := by
  unfold escapeEvent
  simp only [ofPred_exists, ofPred_and]
  exact MeasurableSet.iUnion fun y ↦ (MeasurableSet.const _).inter
    (measurableSet_connectionEvent x y)

lemma escapeEvent_increasing {d : ℕ} (x : Vertex d) (s : Finset (Vertex d)) :
    BK.Increasing (escapeEvent x s) := by
  rintro ω η h ⟨y, hy, hp⟩
  exact ⟨y, hy, SimpleGraph.Reachable.mono (openGraph_mono h) hp⟩

lemma escapeEvent_antitone {d : ℕ} (x : Vertex d) : Antitone (escapeEvent x) := by
  rintro s t hst ω ⟨y, hy, hp⟩
  exact ⟨y, (fun hs ↦ hy (hst hs)), hp⟩

/-- Escape events really do have finite positive witnesses: extract the open
bonds of a finite connecting walk. -/
lemma escapeEvent_eq_iUnion_truncation {d : ℕ} (x : Vertex d) (s : Finset (Vertex d)) :
    escapeEvent x s = ⋃ F : Finset (Bond d), BK.truncation (escapeEvent x s) F := by
  ext ω
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨n, hn⟩ := (graph_reachable_iff_exists_nStep (openGraph ω) x y).mp hp
    obtain ⟨F, _, hopen, hforce⟩ := graphNStep_open_certificate hn
    apply mem_iUnion.mpr
    refine ⟨F, y, hy, ?_⟩
    apply (graph_reachable_iff_exists_nStep _ x y).mpr
    refine ⟨n, hforce _ ?_⟩
    intro e he
    simp [Network.certificateConfiguration, he, hopen e he]
  · intro h
    obtain ⟨F, hF⟩ := mem_iUnion.mp h
    exact BK.truncation_subset (escapeEvent_increasing x s) F hF

/-- Full-lattice escape-event Harris inequality, with no assumed finite-domain
restriction and no positive-association premise. -/
theorem percolation_escape_harris (d : ℕ) (p : unitInterval)
    (x y : Vertex d) (s t : Finset (Vertex d)) :
    percolation d p (escapeEvent x s) * percolation d p (escapeEvent y t) ≤
      percolation d p (escapeEvent x s ∩ escapeEvent y t) :=
  percolation_harris_of_finite_witnesses d p (escapeEvent_increasing x s)
    (escapeEvent_increasing y t) (escapeEvent_eq_iUnion_truncation x s)
    (escapeEvent_eq_iUnion_truncation y t)

end NearCritical
