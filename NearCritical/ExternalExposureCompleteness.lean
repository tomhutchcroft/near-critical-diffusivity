module

public import NearCritical.ExternalSearchGraphBridge
public import NearCritical.ConnectionToSet

/-! Complete finite-edge exploration from the imported exact-exposure compiler.
 No observed-history or expected-cost claim. -/
@[expose] public section
namespace NearCritical.External
open OAI.CriticalPercolation

/-- With one unit of fuel per available edge, exact exposure reaches every
vertex reachable from its root, including the zero-length root connection. -/
theorem exact_exposure_complete {V E : Type*} [DecidableEq V] [DecidableEq E]
    [Fintype E] (G : BondGraph V E) (x : V) (ω : E → Bool) :
    let st : ExactExposure.State V E := ⟨{x}, ∅⟩
    ∀ y, (G.openGraph {e | ω e = true}).Reachable x y →
      y ∈ ((ExactExposure.compile G (Fintype.card E) st).run ω).reached := by
  let st : ExactExposure.State V E := ⟨{x}, ∅⟩
  let final := (ExactExposure.compile G (Fintype.card E) st).run ω
  have hc : ExactExposure.Consistent G st ω := by
    simp [ExactExposure.Consistent, st]
  have hs : ExactExposure.Sound G {x} st ω := by
    intro v hv
    have hvx : v = x := Finset.mem_singleton.mp hv
    subst v
    exact ⟨x, Set.mem_singleton x, .refl x⟩
  have hinv := ExactExposure.compile_invariants G {x} (Fintype.card E) st ω hc hs
  have hcfinal : ExactExposure.Consistent G final ω := hinv.1
  have hx : x ∈ final.reached := hinv.2.2 (Finset.mem_singleton_self x)
  have hexhaust : ¬ ∃ e, ExactExposure.eligible G final e := by
    apply ExactExposure.compile_exhausted
    simp [st]
  have hclosed {v w : V} (hv : v ∈ final.reached)
      (hvw : (G.openGraph {e | ω e = true}).Adj v w) : w ∈ final.reached := by
    obtain ⟨⟨e, he, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvw
    have hvend : v ∈ G.ends e := by rw [heq]; simp
    have hwend : w ∈ G.ends e := by rw [heq]; simp
    have hread : e ∈ final.read := by
      by_contra hnot
      exact hexhaust ⟨e, hnot, v, hv, hvend⟩
    exact hcfinal e hread he w hwend
  have hstay {v w : V} (hvw : (G.openGraph {e | ω e = true}).Reachable v w) :
      v ∈ final.reached → w ∈ final.reached := by
    obtain ⟨walk⟩ := hvw
    induction walk with
    | nil => exact id
    | cons hadj walk ih => exact fun hv => ih (hclosed hv hadj)
  dsimp only
  intro y hy
  exact hstay hy hx

/-- The fully fueled imported exposure recovers exactly the actual restricted
component of its root. No root-in-domain assumption is needed for the isolated
root's zero-length reachability. Event membership imposes its own domain guards. -/
theorem finite_exposure_reached_iff_actual {d : ℕ} (U : Finset (Vertex d))
    (x y : Vertex d) (ω : Configuration d) :
    y ∈ ((ExactExposure.compile (finiteBondSearchGraph (internalBondSet U))
      (internalBondSet U).card (rootExposureState (internalBondSet U) x)).run
        (fun e => ω e.val)).reached ↔
      (restrictedGraph ω (U : Set (Vertex d))).Reachable x y := by
  constructor
  · exact finite_exposure_reached_actual U x (internalBondSet U).card ω y
  · intro hy
    rw [← finite_search_graph_eq_restricted U ω] at hy
    simpa only [Fintype.card_coe, rootExposureState] using
      (exact_exposure_complete (finiteBondSearchGraph (internalBondSet U)) x
        (fun e => ω e.val) y hy)

/-- The actual guarded connection-to-target event is exactly a target hit in
this complete exposure. Domain guards remain explicit, including at time zero. -/
theorem finite_exposure_connection_event_iff {d : ℕ} (U : Finset (Vertex d))
    (x : Vertex d) (A : Set (Vertex d)) (ω : Configuration d) :
    ω ∈ connectionToSetEvent (U : Set (Vertex d)) x A ↔
      x ∈ U ∧ ∃ y ∈ ((ExactExposure.compile
        (finiteBondSearchGraph (internalBondSet U)) (internalBondSet U).card
        (rootExposureState (internalBondSet U) x)).run (fun e => ω e.val)).reached,
          y ∈ A ∧ y ∈ U := by
  constructor
  · rintro ⟨hx, y, hyA, hyU, hxy⟩
    exact ⟨hx, y, (finite_exposure_reached_iff_actual U x y ω).mpr hxy, hyA, hyU⟩
  · rintro ⟨hx, y, hy, hyA, hyU⟩
    exact ⟨hx, y, hyA, hyU, (finite_exposure_reached_iff_actual U x y ω).mp hy⟩

end NearCritical.External
