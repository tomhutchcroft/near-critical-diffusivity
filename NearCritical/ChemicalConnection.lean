module

public import NearCritical.Events

/-! Bounded chemical connections, including a zero-length connection at x = y.
These are full-lattice events, with no finite-domain restriction. -/
@[expose] public section
namespace NearCritical
open MeasureTheory Set

/-- The event that an open walk of at most `m` bonds joins `x` to `y`.
Existence of such a walk is equivalent to existence of a path of length at most `m`. -/
def chemicalConnectionEvent {d : ℕ} (x y : Vertex d) (m : ℕ) :
    Set (Configuration d) :=
  {ω | ∃ n ≤ m, graphNStep (openGraph ω) n x y}

lemma measurableSet_chemicalConnectionEvent {d : ℕ} (x y : Vertex d) (m : ℕ) :
    MeasurableSet (chemicalConnectionEvent x y m) := by
  unfold chemicalConnectionEvent
  simp only [ofPred_exists, ofPred_and]
  exact MeasurableSet.iUnion fun n ↦ (MeasurableSet.const _).inter
    (measurableSet_graphNStep (fun ω ↦ openGraph ω) measurableSet_open_adj n x y)

lemma graphNStep_mono {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    {n : ℕ} {x y : V} (hn : graphNStep G n x y) : graphNStep H n x y := by
  induction n generalizing y with
  | zero => exact hn
  | succ n ih =>
    obtain ⟨z, hz, hzy⟩ := hn
    exact ⟨z, ih hz, h hzy⟩

lemma chemicalConnectionEvent_mono_config {d : ℕ} {ω η : Configuration d}
    (h : ∀ e, ω e = true → η e = true) {x y : Vertex d} {m : ℕ}
    (hω : ω ∈ chemicalConnectionEvent x y m) :
    η ∈ chemicalConnectionEvent x y m := by
  obtain ⟨n, hn, hw⟩ := hω
  exact ⟨n, hn, graphNStep_mono (openGraph_mono h) hw⟩

lemma chemicalConnectionEvent_mono_length {d : ℕ} (x y : Vertex d)
    {m k : ℕ} (h : m ≤ k) :
    chemicalConnectionEvent x y m ⊆ chemicalConnectionEvent x y k := by
  rintro ω ⟨n, hn, hw⟩
  exact ⟨n, hn.trans h, hw⟩

lemma chemicalConnectionEvent_zero {d : ℕ} (x y : Vertex d) :
    chemicalConnectionEvent x y 0 = {_ω | x = y} := by
  ext ω
  simp [chemicalConnectionEvent, graphNStep]

lemma connectionEvent_eq_iUnion_chemical {d : ℕ} (x y : Vertex d) :
    connectionEvent x y = ⋃ m, chemicalConnectionEvent x y m := by
  ext ω
  simp only [connectionEvent, mem_ofPred_eq, graph_reachable_iff_exists_nStep,
    mem_iUnion, chemicalConnectionEvent]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, n, le_rfl, hn⟩
  · rintro ⟨m, n, _, hn⟩
    exact ⟨n, hn⟩

/-- A walk of length n has a forcing certificate of at most n distinct bonds.
The certificate consists entirely of bonds open in the original configuration. -/
lemma graphNStep_open_certificate {d : ℕ} {ω : Configuration d} {n : ℕ}
    {x y : Vertex d} (h : graphNStep (openGraph ω) n x y) :
    ∃ s : Finset (Bond d), s.card ≤ n ∧ (∀ e ∈ s, ω e = true) ∧
      ∀ η : Configuration d, (∀ e ∈ s, η e = true) →
        graphNStep (openGraph η) n x y := by
  classical
  induction n generalizing y with
  | zero => exact ⟨∅, by simp, by simp, fun _ _ ↦ h⟩
  | succ n ih =>
    obtain ⟨z, hz, e, he, hzy⟩ := h
    obtain ⟨s, hs, hopen, hforce⟩ := ih hz
    refine ⟨insert e s, (Finset.card_insert_le e s).trans (Nat.add_le_add_right hs 1),
      ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he
      · exact hopen f hf
    · intro η hη
      exact ⟨z, hforce η (fun f hf ↦ hη f (Finset.mem_insert_of_mem hf)),
        e, hη e (Finset.mem_insert_self e s), hzy⟩

lemma chemicalConnectionEvent_open_certificate {d : ℕ} {ω : Configuration d}
    {x y : Vertex d} {m : ℕ} (h : ω ∈ chemicalConnectionEvent x y m) :
    ∃ s : Finset (Bond d), s.card ≤ m ∧ (∀ e ∈ s, ω e = true) ∧
      ∀ η : Configuration d, (∀ e ∈ s, η e = true) →
        η ∈ chemicalConnectionEvent x y m := by
  obtain ⟨n, hn, hw⟩ := h
  obtain ⟨s, hs, hopen, hforce⟩ := graphNStep_open_certificate hw
  exact ⟨s, hs.trans hn, hopen, fun η hη ↦ ⟨n, hn, hforce η hη⟩⟩

end NearCritical
