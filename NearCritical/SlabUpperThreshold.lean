module

public import NearCritical.OpenEventHarris
public import NearCritical.Slab

/-! Threshold bridge for source prop.slab.upper (source 6069–6106).

The source proof produces, at `p = pc + λ n⁻²`, an infinite `p`-open cluster
SOMEWHERE in the slab with positive probability. The project threshold
`restrictedCriticalPoint` is defined through the restricted cluster of the
ORIGIN. This leaf closes that gap with no new hypothesis on the law:

* a countable union reduces "some vertex" to one vertex `x ∈ S` with positive mass;
* a finite set of bonds forcing an `S`-path from `0` to `x` has mass `p^|F| > 0`;
* positive association (Harris) between that cylinder and the restricted
  infinite-cluster event at `x`, proved through restricted escape events with
  finite open witnesses (reusing `percolation_harris_of_finite_witnesses`).

The only geometric input is that every vertex of `S` is joined to `0` inside `S`
in the all-open configuration. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- The restricted graph is monotone in the configuration. -/
lemma restrictedGraph_config_mono {d : ℕ} {ω η : Configuration d}
    (h : ∀ e, ω e = true → η e = true) (S : Set (Vertex d)) :
    restrictedGraph ω S ≤ restrictedGraph η S := by
  rintro x y ⟨hxy, hx, hy⟩
  exact ⟨openGraph_mono h hxy, hx, hy⟩

/-- A vertex outside `S` is isolated in the restricted graph. -/
lemma restricted_reachable_eq_of_not_mem {d : ℕ} {ω : Configuration d}
    {S : Set (Vertex d)} {x y : Vertex d} (hx : x ∉ S)
    (h : (restrictedGraph ω S).Reachable x y) : y = x := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons h _ =>
    obtain ⟨_, hxS, _⟩ := h
    exact absurd hxS hx

/-- Infinite `S`-restricted cluster at an arbitrary vertex. -/
def restrictedInfiniteAtEvent {d : ℕ} (S : Set (Vertex d)) (x : Vertex d) :
    Set (Configuration d) :=
  {ω | {y | (restrictedGraph ω S).Reachable x y}.Infinite}

/-- Some vertex has an infinite `S`-restricted cluster. -/
def restrictedSomeInfiniteEvent {d : ℕ} (S : Set (Vertex d)) : Set (Configuration d) :=
  {ω | ∃ x, {y | (restrictedGraph ω S).Reachable x y}.Infinite}

lemma restrictedSomeInfiniteEvent_eq_iUnion {d : ℕ} (S : Set (Vertex d)) :
    restrictedSomeInfiniteEvent S = ⋃ x, restrictedInfiniteAtEvent S x := by
  ext ω
  exact ⟨fun ⟨x, hx⟩ ↦ mem_iUnion.mpr ⟨x, hx⟩,
    fun h ↦ let ⟨x, hx⟩ := mem_iUnion.mp h; ⟨x, hx⟩⟩

lemma restrictedInfiniteAtEvent_eq_empty_of_not_mem {d : ℕ} {S : Set (Vertex d)}
    {x : Vertex d} (hx : x ∉ S) : restrictedInfiniteAtEvent S x = ∅ := by
  ext ω
  constructor
  · intro hinf
    have hinf' : {y | (restrictedGraph ω S).Reachable x y}.Infinite := hinf
    exact absurd ((Set.finite_singleton x).subset
      (fun y hy ↦ restricted_reachable_eq_of_not_mem hx hy)) hinf'
  · intro h
    simp at h

/-- Restricted walks have finite open forcing certificates. -/
lemma restricted_graphNStep_open_certificate {d : ℕ} {ω : Configuration d}
    {S : Set (Vertex d)} {n : ℕ} {x y : Vertex d}
    (h : graphNStep (restrictedGraph ω S) n x y) :
    ∃ s : Finset (Bond d), (∀ e ∈ s, ω e = true) ∧
      ∀ η : Configuration d, (∀ e ∈ s, η e = true) →
        graphNStep (restrictedGraph η S) n x y := by
  induction n generalizing y with
  | zero => exact ⟨∅, by simp, fun _ _ ↦ h⟩
  | succ n ih =>
    obtain ⟨z, hz, ⟨e, he, hzy⟩, hzS, hyS⟩ := h
    obtain ⟨s, hopen, hforce⟩ := ih hz
    refine ⟨insert e s, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he
      · exact hopen f hf
    · intro η hη
      exact ⟨z, hforce η (fun f hf ↦ hη f (Finset.mem_insert_of_mem hf)),
        ⟨e, hη e (Finset.mem_insert_self e s), hzy⟩, hzS, hyS⟩

/-- A restricted open path from `x` to outside a finite vertex set. -/
def restrictedEscapeEvent {d : ℕ} (S : Set (Vertex d)) (x : Vertex d)
    (s : Finset (Vertex d)) : Set (Configuration d) :=
  {ω | ∃ y, y ∉ s ∧ (restrictedGraph ω S).Reachable x y}

lemma measurableSet_restrictedEscapeEvent {d : ℕ} (S : Set (Vertex d)) (x : Vertex d)
    (s : Finset (Vertex d)) : MeasurableSet (restrictedEscapeEvent S x s) := by
  unfold restrictedEscapeEvent
  simp only [ofPred_exists, ofPred_and]
  exact MeasurableSet.iUnion fun y ↦ (MeasurableSet.const _).inter
    (measurableSet_graphReachable (fun ω ↦ restrictedGraph ω S)
      (measurableSet_restricted_adj S) x y)

lemma restrictedEscapeEvent_increasing {d : ℕ} (S : Set (Vertex d)) (x : Vertex d)
    (s : Finset (Vertex d)) : BK.Increasing (restrictedEscapeEvent S x s) := by
  rintro ω η h ⟨y, hy, hp⟩
  exact ⟨y, hy, SimpleGraph.Reachable.mono (restrictedGraph_config_mono h S) hp⟩

lemma restrictedEscapeEvent_antitone {d : ℕ} (S : Set (Vertex d)) (x : Vertex d) :
    Antitone (restrictedEscapeEvent S x) := by
  rintro s t hst ω ⟨y, hy, hp⟩
  exact ⟨y, (fun hs ↦ hy (hst hs)), hp⟩

lemma restrictedEscapeEvent_eq_iUnion_truncation {d : ℕ} (S : Set (Vertex d))
    (x : Vertex d) (s : Finset (Vertex d)) :
    restrictedEscapeEvent S x s =
      ⋃ F : Finset (Bond d), BK.truncation (restrictedEscapeEvent S x s) F := by
  ext ω
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨n, hn⟩ := (graph_reachable_iff_exists_nStep _ x y).mp hp
    obtain ⟨F, hopen, hforce⟩ := restricted_graphNStep_open_certificate hn
    apply mem_iUnion.mpr
    refine ⟨F, y, hy, ?_⟩
    apply (graph_reachable_iff_exists_nStep _ x y).mpr
    refine ⟨n, hforce _ ?_⟩
    intro e he
    simp [Network.certificateConfiguration, he, hopen e he]
  · intro h
    obtain ⟨F, hF⟩ := mem_iUnion.mp h
    exact BK.truncation_subset (restrictedEscapeEvent_increasing S x s) F hF

lemma restrictedInfiniteAtEvent_eq_iInter_escape {d : ℕ} (S : Set (Vertex d))
    (x : Vertex d) :
    restrictedInfiniteAtEvent S x = ⋂ s : Finset (Vertex d), restrictedEscapeEvent S x s := by
  ext ω
  simp only [restrictedInfiniteAtEvent, mem_ofPred_eq, infinite_iff_escape_finsets,
    mem_iInter, restrictedEscapeEvent]
  constructor
  · intro h s
    obtain ⟨y, hy, hys⟩ := h s
    exact ⟨y, hys, hy⟩
  · intro h s
    obtain ⟨y, hys, hy⟩ := h s
    exact ⟨y, hy, hys⟩

/-- All bonds of a finite set are open. -/
def bondsOpenEvent {d : ℕ} (F : Finset (Bond d)) : Set (Configuration d) :=
  Set.pi (F : Set (Bond d)) (fun _ ↦ ({true} : Set Bool))

lemma mem_bondsOpenEvent {d : ℕ} {F : Finset (Bond d)} {η : Configuration d} :
    η ∈ bondsOpenEvent F ↔ ∀ e ∈ F, η e = true := by
  simp [bondsOpenEvent, Set.mem_pi]

lemma measurableSet_bondsOpenEvent {d : ℕ} (F : Finset (Bond d)) :
    MeasurableSet (bondsOpenEvent F) :=
  MeasurableSet.pi F.countable_toSet (fun _ _ ↦ measurableSet_singleton true)

lemma bondsOpenEvent_increasing {d : ℕ} (F : Finset (Bond d)) :
    BK.Increasing (bondsOpenEvent F) := by
  intro η θ h hη
  rw [mem_bondsOpenEvent] at hη ⊢
  exact fun e he ↦ h e (hη e he)

lemma bondsOpenEvent_eq_iUnion_truncation {d : ℕ} (F : Finset (Bond d)) :
    bondsOpenEvent F = ⋃ G : Finset (Bond d), BK.truncation (bondsOpenEvent F) G := by
  ext η
  constructor
  · intro hη
    apply mem_iUnion.mpr
    refine ⟨F, ?_⟩
    change Network.certificateConfiguration η (F : Set (Bond d)) ∈ bondsOpenEvent F
    rw [mem_bondsOpenEvent] at hη ⊢
    intro e he
    simp [Network.certificateConfiguration, he, hη e he]
  · intro h
    obtain ⟨G, hG⟩ := mem_iUnion.mp h
    exact BK.truncation_subset (bondsOpenEvent_increasing F) G hG

/-- A finite open cylinder has positive mass at every positive parameter. -/
lemma percolation_bondsOpenEvent_ne_zero {d : ℕ} (p : unitInterval) (hp : 0 < (p : ℝ))
    (F : Finset (Bond d)) : percolation d p (bondsOpenEvent F) ≠ 0 := by
  unfold bondsOpenEvent
  rw [percolation_open_cylinder]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ (ENNReal.ofReal_pos.mpr hp).ne'

/-- Harris between a finite open cylinder and an actual restricted infinite
cluster, via restricted escape events (no finite witness for the infinite event
is assumed). -/
theorem bondsOpen_restrictedInfinite_harris {d : ℕ} (p : unitInterval)
    (S : Set (Vertex d)) (F : Finset (Bond d)) (x : Vertex d) :
    percolation d p (bondsOpenEvent F) * percolation d p (restrictedInfiniteAtEvent S x) ≤
      percolation d p (bondsOpenEvent F ∩ restrictedInfiniteAtEvent S x) := by
  let C := fun s : Finset (Vertex d) ↦ bondsOpenEvent F ∩ restrictedEscapeEvent S x s
  have hCmeas : ∀ s, MeasurableSet (C s) := fun s ↦
    (measurableSet_bondsOpenEvent F).inter (measurableSet_restrictedEscapeEvent S x s)
  have hdir : Directed (· ⊇ ·) C := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact inter_subset_inter subset_rfl
        (restrictedEscapeEvent_antitone S x Finset.subset_union_left)
    · exact inter_subset_inter subset_rfl
        (restrictedEscapeEvent_antitone S x Finset.subset_union_right)
  have hCeq : bondsOpenEvent F ∩ restrictedInfiniteAtEvent S x = ⋂ s, C s := by
    rw [restrictedInfiniteAtEvent_eq_iInter_escape]
    ext ω
    simp [C, forall_and]
  rw [hCeq, hdir.measure_iInter (fun s ↦ (hCmeas s).nullMeasurableSet)
    ⟨∅, measure_ne_top _ _⟩]
  apply le_iInf
  intro s
  calc
    _ ≤ percolation d p (bondsOpenEvent F) *
        percolation d p (restrictedEscapeEvent S x s) := by
      apply mul_le_mul' le_rfl
      apply measure_mono
      rw [restrictedInfiniteAtEvent_eq_iInter_escape]
      exact iInter_subset _ s
    _ ≤ _ := percolation_harris_of_finite_witnesses d p (bondsOpenEvent_increasing F)
        (restrictedEscapeEvent_increasing S x s) (bondsOpenEvent_eq_iUnion_truncation F)
        (restrictedEscapeEvent_eq_iUnion_truncation S x s)

/-- Positive mass of the ORIGIN's restricted infinite cluster from positive mass of
an infinite restricted cluster anywhere, when `S` is all-open-connected to `0`. -/
theorem restrictedInfiniteEvent_ne_zero_of_someInfinite {d : ℕ} (S : Set (Vertex d))
    (p : unitInterval) (hp : 0 < (p : ℝ))
    (hconn : ∀ x ∈ S, (restrictedGraph (fun _ ↦ true) S).Reachable 0 x)
    (hpos : percolation d p (restrictedSomeInfiniteEvent S) ≠ 0) :
    percolation d p (restrictedInfiniteEvent d S) ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, percolation d p (restrictedInfiniteAtEvent S x) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hpos
    rw [restrictedSomeInfiniteEvent_eq_iUnion]
    exact measure_iUnion_null h
  have hxS : x ∈ S := by
    by_contra hxS
    apply hx
    rw [restrictedInfiniteAtEvent_eq_empty_of_not_mem hxS, measure_empty]
  obtain ⟨n, hn⟩ := (graph_reachable_iff_exists_nStep _ 0 x).mp (hconn x hxS)
  obtain ⟨F, -, hforce⟩ := restricted_graphNStep_open_certificate hn
  have hsub : bondsOpenEvent F ∩ restrictedInfiniteAtEvent S x ⊆
      restrictedInfiniteEvent d S := by
    rintro ω ⟨hF, hinf⟩
    rw [mem_bondsOpenEvent] at hF
    have h0x : (restrictedGraph ω S).Reachable 0 x :=
      (graph_reachable_iff_exists_nStep _ 0 x).mpr ⟨n, hforce ω hF⟩
    have hinf' : {y | (restrictedGraph ω S).Reachable x y}.Infinite := hinf
    show {y | (restrictedGraph ω S).Reachable 0 y}.Infinite
    exact Set.Infinite.mono (fun y hy ↦ h0x.trans hy) hinf'
  intro h0
  have hle := (bondsOpen_restrictedInfinite_harris p S F x).trans (measure_mono hsub)
  rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at hle
  exact hle.elim (percolation_bondsOpenEvent_ne_zero p hp F) hx

/-- Threshold bridge: an infinite restricted cluster somewhere, with positive
probability at a positive parameter `p`, places the actual restricted critical
point at or below `p`. -/
theorem restrictedCriticalPoint_le_of_someInfinite {d : ℕ} (S : Set (Vertex d))
    (p : unitInterval) (hp : 0 < (p : ℝ))
    (hconn : ∀ x ∈ S, (restrictedGraph (fun _ ↦ true) S).Reachable 0 x)
    (hpos : percolation d p (restrictedSomeInfiniteEvent S) ≠ 0) :
    restrictedCriticalPoint d S ≤ p := by
  have h0 := restrictedInfiniteEvent_ne_zero_of_someInfinite S p hp hconn hpos
  have hdens : 0 < restrictedDensity d S p :=
    ENNReal.toReal_pos h0 (measure_ne_top _ _)
  unfold restrictedCriticalPoint
  exact sInf_le (show p ∈ {q | 0 < restrictedDensity d S q} from hdens)

end NearCritical
