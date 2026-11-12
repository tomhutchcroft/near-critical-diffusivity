module

public import NearCritical.OpenEventHarris
public import NearCritical.TranslationInvariance
public import NearCritical.PercolationMonotonicity

/-! Genuine infinite-cluster positive association by measurable escape limits.
This is ordinary intersection, not finite-forcing disjoint occurrence. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Infinite cluster membership at an arbitrary vertex. -/
def infiniteClusterAtEvent {d : ℕ} (x : Vertex d) : Set (Configuration d) :=
  {ω | (cluster ω x).Infinite}

@[simp] lemma infiniteClusterAtEvent_zero (d : ℕ) :
    infiniteClusterAtEvent (0 : Vertex d) = infiniteClusterEvent d := rfl

lemma measurableSet_infiniteClusterAtEvent {d : ℕ} (x : Vertex d) :
    MeasurableSet (infiniteClusterAtEvent x) :=
  measurableSet_graphInfiniteCluster (fun ω ↦ openGraph ω) measurableSet_open_adj x

/-- An infinite cluster escapes every finite vertex set, and conversely. -/
lemma infiniteClusterAtEvent_eq_iInter_escape {d : ℕ} (x : Vertex d) :
    infiniteClusterAtEvent x = ⋂ s : Finset (Vertex d), escapeEvent x s := by
  ext ω
  simp only [infiniteClusterAtEvent, mem_ofPred_eq, infinite_iff_escape_finsets,
    mem_iInter, escapeEvent, cluster]
  constructor
  · intro h s
    obtain ⟨y, hy, hys⟩ := h s
    exact ⟨y, hys, hy⟩
  · intro h s
    obtain ⟨y, hys, hy⟩ := h s
    exact ⟨y, hy, hys⟩

/-- Harris for actual infinite-cluster membership. In particular, this bound is
not obtained by pretending an infinite cluster has a finite forcing witness. -/
theorem percolation_infiniteCluster_harris (d : ℕ) (p : unitInterval)
    (x y : Vertex d) :
    percolation d p (infiniteClusterAtEvent x) *
      percolation d p (infiniteClusterAtEvent y) ≤
      percolation d p (infiniteClusterAtEvent x ∩ infiniteClusterAtEvent y) := by
  let C := fun s : Finset (Vertex d) ↦ escapeEvent x s ∩ escapeEvent y s
  have hCmeas : ∀ s, MeasurableSet (C s) := fun s ↦
    (measurableSet_escapeEvent x s).inter (measurableSet_escapeEvent y s)
  have hdir : Directed (· ⊇ ·) C := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact inter_subset_inter (escapeEvent_antitone x Finset.subset_union_left)
        (escapeEvent_antitone y Finset.subset_union_left)
    · exact inter_subset_inter (escapeEvent_antitone x Finset.subset_union_right)
        (escapeEvent_antitone y Finset.subset_union_right)
  have hCeq : infiniteClusterAtEvent x ∩ infiniteClusterAtEvent y = ⋂ s, C s := by
    rw [infiniteClusterAtEvent_eq_iInter_escape, infiniteClusterAtEvent_eq_iInter_escape]
    ext ω
    simp [C, forall_and]
  rw [hCeq, hdir.measure_iInter (fun s ↦ (hCmeas s).nullMeasurableSet)
    ⟨∅, measure_ne_top _ _⟩]
  apply le_iInf
  intro s
  calc
    _ ≤ percolation d p (escapeEvent x s) * percolation d p (escapeEvent y s) := by
      apply mul_le_mul' <;> apply measure_mono
      · rw [infiniteClusterAtEvent_eq_iInter_escape]
        exact iInter_subset _ s
      · rw [infiniteClusterAtEvent_eq_iInter_escape]
        exact iInter_subset _ s
    _ ≤ _ := percolation_escape_harris d p x y s s

lemma cluster_translate_image {d : ℕ} (a x : Vertex d) (ω : Configuration d) :
    cluster ω (a + x) = (fun z ↦ a + z) '' cluster (translateConfiguration a ω) x := by
  ext z
  obtain ⟨y, rfl⟩ := (Equiv.addLeft a).surjective z
  constructor
  · intro h
    exact ⟨y, (translationGraphIso a ω).reachable_iff.mp h, rfl⟩
  · rintro ⟨y', hy', heq⟩
    have he : y' = y := add_left_cancel heq
    subst y'
    exact (translationGraphIso a ω).reachable_iff.mpr hy'

lemma infiniteClusterAtEvent_translation {d : ℕ} (a x : Vertex d) :
    translateConfiguration a ⁻¹' infiniteClusterAtEvent x = infiniteClusterAtEvent (a + x) := by
  ext ω
  change (cluster (translateConfiguration a ω) x).Infinite ↔ (cluster ω (a + x)).Infinite
  rw [cluster_translate_image]
  exact (Set.infinite_image_iff (Equiv.addLeft a).injective.injOn).symm

/-- Stationarity identifies arbitrary-vertex infinite-cluster mass with theta. -/
theorem infiniteClusterAtEvent_probability (d : ℕ) (p : unitInterval) (x : Vertex d) :
    (percolation d p).real (infiniteClusterAtEvent x) = density d p := by
  have he : translateConfiguration x ⁻¹' infiniteClusterAtEvent (0 : Vertex d) =
      infiniteClusterAtEvent x := by simpa using infiniteClusterAtEvent_translation x 0
  rw [← he, ← map_measureReal_apply (measurable_translateConfiguration x)
    (measurableSet_infiniteClusterAtEvent 0), percolation_map_translation]
  rfl

/-- The concrete FKG input used by source lem.chem.converse:
P_p[x and y both belong to infinite clusters] >= theta(p)^2. No uniqueness
assertion is needed for this intersection bound. -/
theorem infiniteCluster_intersection_probability (d : ℕ) (p : unitInterval)
    (x y : Vertex d) :
    density d p ^ 2 ≤
      (percolation d p).real (infiniteClusterAtEvent x ∩ infiniteClusterAtEvent y) := by
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (percolation_infiniteCluster_harris d p x y)
  rw [ENNReal.toReal_mul] at h
  change (percolation d p).real (infiniteClusterAtEvent x) *
    (percolation d p).real (infiniteClusterAtEvent y) ≤
      (percolation d p).real (infiniteClusterAtEvent x ∩ infiniteClusterAtEvent y) at h
  simpa only [infiniteClusterAtEvent_probability, pow_two] using h

/-- The two infinite-cluster membership events have a strictly positive
intersection at every strictly supercritical parameter. -/
theorem supercritical_infiniteCluster_intersection_pos {d : ℕ} {p : unitInterval}
    (hp : criticalPoint d < p) (x y : Vertex d) :
    0 < (percolation d p).real (infiniteClusterAtEvent x ∩ infiniteClusterAtEvent y) :=
  lt_of_lt_of_le (pow_pos (density_pos_above_critical hp) 2)
    (infiniteCluster_intersection_probability d p x y)

end NearCritical
