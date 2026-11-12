module

public import NearCritical.Section10Trajectories

/-! `lem.nw.path`, per trajectory, with edge provenance (deterministic core).

The existing `chainSurvives_geometry` / `semanticRule_certificate` show that
SOME surviving chain has a short microscopic path. The flow of `prop.nw.main`
needs more: EVERY trajectory of positive weight carries a walk, and every edge
of that walk is charged to a cluster of a nest visited by the trajectory or to
the bridge of one of its steps. This file is that bookkeeping.

* `trajEdges Ecl Ebr m t x f`: the edges available to the trajectory
  `x, f 0, f 1, ...`: the cluster edges `Ecl` of every visited state and the
  bridge edges `Ebr s x_s x_{s+1}` of every step.
* `trajectory_walk`: if every positive step maps the invariant forward and
  connects, for every cluster of the new nest, the whole boundary of some
  cluster of the old nest to that cluster by a walk using old-cluster and
  bridge edges (`hstep`; a stay uses the empty walk), and the last positive
  step from an invariant state gives a walk inside a cluster to an exit edge
  (`hexit`), then for every trajectory `f` of positive weight ending at the
  exit time there is a cluster `c` of the initial nest such that every boundary
  point of `c` is joined to an exit edge by a walk with edges in
  `trajEdges`.
-/

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

variable {d : ℕ} {X ι V : Type*}

/-- Edges available to a trajectory: cluster edges of visited states and
bridge edges of its steps. -/
def trajEdges (Ecl : X → Set (Sym2 V)) (Ebr : ℕ → X → X → Set (Sym2 V)) :
    (m : ℕ) → ℕ → X → (Fin m → X) → Set (Sym2 V)
  | 0, _, x, _ => Ecl x
  | m+1, t, x, f => Ecl x ∪ Ebr t x (f 0) ∪ trajEdges Ecl Ebr m (t+1) (f 0) (Fin.tail f)

lemma trajEdges_self (Ecl : X → Set (Sym2 V)) (Ebr : ℕ → X → X → Set (Sym2 V)) :
    ∀ (m t : ℕ) (x : X) (f : Fin m → X), Ecl x ⊆ trajEdges Ecl Ebr m t x f
  | 0, _, _, _ => fun _ h => h
  | _+1, _, _, _ => fun _ h => Or.inl (Or.inl h)

theorem trajectory_walk (G : SimpleGraph V)
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk0 : ∀ t x y z, 0 ≤ k t x y z) (z : Configuration d × Configuration d)
    (cl : X → Set ι) (bd : ℕ → ι → Set V) (Inv : ℕ → X → Prop)
    (Ecl : X → Set (Sym2 V)) (Ebr : ℕ → X → X → Set (Sym2 V))
    (exitV : V → Prop) (T : ℕ)
    (hexit : ∀ x y, Inv T x → 0 < k T x y z →
      ∃ c ∈ cl x, ∀ pt ∈ bd T c, ∃ v w, exitV w ∧ G.Adj v w ∧
        ∃ W : G.Walk pt v, ∀ e ∈ W.edges, e ∈ Ecl x)
    (hstep : ∀ t, t < T → ∀ x y, Inv t x → 0 < k t x y z →
      Inv (t+1) y ∧ ∀ c' ∈ cl y, ∃ c ∈ cl x, ∀ pt ∈ bd t c, ∃ v ∈ bd (t+1) c',
        ∃ W : G.Walk pt v, ∀ e ∈ W.edges, e ∈ Ecl x ∪ Ebr t x y) :
    ∀ (m t : ℕ) (x : X) (f : Fin (m+1) → X), t + m = T → Inv t x →
      0 < trajWeight k (m+1) t x f z →
      ∃ c ∈ cl x, ∀ pt ∈ bd t c, ∃ v w, exitV w ∧ G.Adj v w ∧
        ∃ W : G.Walk pt v, ∀ e ∈ W.edges, e ∈ trajEdges Ecl Ebr (m+1) t x f := by
  intro m
  induction m with
  | zero =>
    intro t x f ht hI hw
    have htT : t = T := by omega
    subst htT
    have hk : 0 < k t x (f 0) z := by
      have h : 0 < k t x (f 0) z * 1 := hw
      simpa using h
    obtain ⟨c, hc, hwalk⟩ := hexit x (f 0) hI hk
    refine ⟨c, hc, fun pt hpt => ?_⟩
    obtain ⟨v, w, hw1, hadj, W, hW⟩ := hwalk pt hpt
    exact ⟨v, w, hw1, hadj, W, fun e he => trajEdges_self Ecl Ebr _ _ _ _ (hW e he)⟩
  | succ m ih =>
    intro t x f ht hI hw
    have hw' : 0 < k t x (f 0) z * trajWeight k (m+1) (t+1) (f 0) (Fin.tail f) z := hw
    have hrest0 : 0 ≤ trajWeight k (m+1) (t+1) (f 0) (Fin.tail f) z :=
      trajWeight_nonneg k hk0 _ _ _ _ z
    have hk : 0 < k t x (f 0) z := by
      rcases (hk0 t x (f 0) z).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hw'
        exact absurd hw' (lt_irrefl _)
    have hrest : 0 < trajWeight k (m+1) (t+1) (f 0) (Fin.tail f) z := by
      rcases hrest0.lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hw'
        exact absurd hw' (lt_irrefl _)
    obtain ⟨hI', hconn⟩ := hstep t (by omega) x (f 0) hI hk
    obtain ⟨c', hc', hwalk'⟩ := ih (t+1) (f 0) (Fin.tail f) (by omega) hI' hrest
    obtain ⟨c, hc, hfirst⟩ := hconn c' hc'
    refine ⟨c, hc, fun pt hpt => ?_⟩
    obtain ⟨v, hv, W1, hW1⟩ := hfirst pt hpt
    obtain ⟨v', w, hw1, hadj, W2, hW2⟩ := hwalk' v hv
    refine ⟨v', w, hw1, hadj, W1.append W2, fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl (hW1 e he)
    · exact Or.inr (hW2 e he)

end NearCritical.Section10
