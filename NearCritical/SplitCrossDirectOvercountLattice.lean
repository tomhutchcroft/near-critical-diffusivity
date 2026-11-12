module

public import NearCritical.SplitCrossDirectCrossing
public import NearCritical.SplitCrossDirectOvercount

/-! Lattice overcount (item C of the direct proof of `SplitCrossInput`,
deterministic part R3).

`Layout.real_real_false`: let `θ` be realised by two tuples `β, β'` with the
same terminals, and let `v₀` be a node such that the arm and tip vertices of
`β'` at `v₀` are not removed vertices of `β`. Under the combinatorial
hypotheses on the layout (the port graph is connected; a side labelling of
the tree around `v₀`; three ports with fixed positions on the three sides;
every tip belongs to an edge) and the separation of the arms of `β'`, this is
impossible.

So for every node `v₀` some arm vertex of `β'` at `v₀` is a removed vertex of
`β`: the two node positions are within `2R` of each other, and only boundedly
many tuples are realised.

Proof: `overcount_contradiction` with index graph the port graph of `β`,
representatives the port positions, `G'` the open graph of `θ` in `Λ` with the
star of `β'` at `v₀` closed, the exceptional edge the one whose outside-cluster
contains that star, and labels the membership in the three sides
`A k` (outside-clusters of `β'`-edges on side `k`, and arms of `β'`-nodes on
side `k`), which are closed under `G'`-adjacency and pairwise disjoint.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

lemma pairwise_pmap_forall {α γ : Type*} {P : α → Prop} (f : ∀ a, P a → γ) (R : γ → γ → Prop)
    (hsymm : ∀ x y, R x y → R y x) : ∀ (l : List α) (H : ∀ a ∈ l, P a),
      (l.pmap f H).Pairwise R →
      ∀ a (ha : a ∈ l) b (hb : b ∈ l), a ≠ b → R (f a (H a ha)) (f b (H b hb))
  | [], _, _ => fun a ha => absurd ha List.not_mem_nil
  | x :: l, H, hp => by
    have hp' : (f x (H x (by simp)) :: l.pmap f (fun a ha => H a (List.mem_cons_of_mem _ ha))).Pairwise
        R := hp
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hp'
    have ih := pairwise_pmap_forall f R hsymm l (fun a ha => H a (List.mem_cons_of_mem _ ha)) h2
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact h1 _ (List.mem_pmap.mpr ⟨b, hb', rfl⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact hsymm _ _ (h1 _ (List.mem_pmap.mpr ⟨a, ha', rfl⟩))
      · exact ih a ha' b hb' hab

/-- Close the bonds of `F`. -/
def closeBonds (θ : Configuration d) (F : Finset (Bond d)) : Configuration d :=
  fun e => if e ∈ F then false else θ e

lemma closeBonds_true {θ : Configuration d} {F : Finset (Bond d)} {e : Bond d}
    (h : closeBonds θ F e = true) : e ∉ F ∧ θ e = true := by
  unfold closeBonds at h
  by_cases he : e ∈ F
  · rw [if_pos he] at h
    exact absurd h (by simp)
  · rw [if_neg he] at h
    exact ⟨he, h⟩

lemma closeBonds_of_notMem {θ : Configuration d} {F : Finset (Bond d)} {e : Bond d}
    (he : e ∉ F) (h : θ e = true) : closeBonds θ F e = true := by
  unfold closeBonds
  rw [if_neg he]
  exact h

namespace Layout

variable {Node Term : Type} [Fintype Node] (L : Layout d Node Term)

/-- The outside-cluster of an edge. -/
def cl (β : Node → Vertex d) (y : Term → Vertex d) (θ : Configuration d)
    (e : Port Node Term × Port Node Term) : Finset (Vertex d) :=
  finiteBoxCluster θ (L.Uout β) (L.pos β y e.1)

theorem real_ports_mem_cl {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) {e : Port Node Term × Port Node Term} (he : e ∈ L.edges) :
    L.pos β y e.1 ∈ L.cl β y θ e ∧ L.pos β y e.2 ∈ L.cl β y θ e := by
  refine ⟨root_mem_finiteBoxCluster θ _ (hpos e he), ?_⟩
  obtain ⟨_, z, hz, hzT, hreach⟩ := L.real_edge_conn hθ he
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact (mem_finiteBoxCluster θ _ _ _).mpr ⟨Finset.mem_coe.mp hzT.2,
    Reachable.mono (restrictedGraph_mono θ Set.inter_subset_right) hreach⟩

theorem real_cl_disjoint {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) {e e' : Port Node Term × Port Node Term}
    (he : e ∈ L.edges) (he' : e' ∈ L.edges) (hne : e ≠ e') :
    Disjoint (L.cl β y θ e) (L.cl β y θ e') := by
  have hp := hθ.2.2
  unfold tedges at hp
  rw [List.pairwise_map] at hp
  exact pairwise_pmap_forall _ _ (fun _ _ h => h.symm) L.edges hpos hp e he e' he' hne

/-- The port graph: edges, and tips of the same node. -/
def portGraph : SimpleGraph (Port Node Term) :=
  SimpleGraph.fromRel fun P Q =>
    (P, Q) ∈ L.edges ∨ ∃ (v : Node) (j j' : Fin 3), P = Port.tip v j ∧ Q = Port.tip v j'

set_option maxHeartbeats 3200000 in
/-- **Two realised tuples cannot differ far at a node.** -/
theorem real_real_false {β β' : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β}
    {hpos' : ∀ e ∈ L.edges, L.pos β' y e.1 ∈ L.Uout β'} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) (hθ' : θ ∈ L.Real β' y hpos') (v₀ : Node)
    (hT : L.portGraph.Preconnected)
    (hΛβ : ∀ v j k, k ≤ L.R → rayPt (β v) (L.ax j) k ∈ L.Λ)
    (hΛβ' : ∀ v j k, k ≤ L.R → rayPt (β' v) (L.ax j) k ∈ L.Λ)
    (hfar : ∀ j k, k ≤ L.R → rayPt (β' v₀) (L.ax j) k ∉ L.Rm β)
    (hsep' : ∀ u u' : Node, u ≠ u' → ∀ j j' k k', k < L.R → k' < L.R →
      rayPt (β' u) (L.ax j) k ≠ rayPt (β' u') (L.ax j') k')
    (htipedge : ∀ u j, ∃ e ∈ L.edges, e.1 = Port.tip u j ∨ e.2 = Port.tip u j)
    (sideN : Node → Fin 3) (sideE : Port Node Term × Port Node Term → Fin 3)
    (hside : ∀ e ∈ L.edges, ∀ u j, (e.1 = Port.tip u j ∨ e.2 = Port.tip u j) → u ≠ v₀ →
      sideE e = sideN u)
    (Tk : Fin 3 → Port Node Term) (ek : Fin 3 → Port Node Term × Port Node Term)
    (hek : ∀ k, ek k ∈ L.edges ∧ ((ek k).1 = Tk k ∨ (ek k).2 = Tk k) ∧ sideE (ek k) = k)
    (hTk : ∀ k, L.pos β y (Tk k) = L.pos β' y (Tk k)) : False := by
  -- the far star
  obtain ⟨F, hFdef⟩ : ∃ F : Finset (Bond d),
      F = Finset.univ.biUnion fun j : Fin 3 => armBonds (β' v₀) (L.ax j) L.R := ⟨_, rfl⟩
  have hFmem : ∀ b : Bond d, b ∈ F ↔ ∃ j k, k < L.R ∧ b = (rayPt (β' v₀) (L.ax j) k, L.ax j) := by
    intro b
    rw [hFdef]
    constructor
    · intro h
      obtain ⟨j, _, hb⟩ := Finset.mem_biUnion.mp h
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨j, k, Finset.mem_range.mp hk, rfl⟩
    · rintro ⟨j, k, hk, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩
  -- the cluster of the far star in the outside domain of `β`
  obtain ⟨Γ₀, hΓ₀def⟩ : ∃ Γ₀ : Finset (Vertex d),
      Γ₀ = finiteBoxCluster θ (L.Uout β) (β' v₀) := ⟨_, rfl⟩
  have hUβ : ∀ j k, k ≤ L.R → rayPt (β' v₀) (L.ax j) k ∈ L.Uout β :=
    fun j k hk => Finset.mem_sdiff.mpr ⟨hΛβ' v₀ j k hk, hfar j k hk⟩
  have hΓ₀ : ∀ j k, k ≤ L.R → rayPt (β' v₀) (L.ax j) k ∈ Γ₀ := by
    intro j k hk
    rw [hΓ₀def]
    refine (mem_finiteBoxCluster θ _ _ _).mpr ⟨hUβ j k hk, ?_⟩
    exact arm_reachable (ω := θ) (S := (L.Uout β : Set (Vertex d))) (β' v₀) (L.ax j) k
      (fun i hi => L.real_arm_open hθ' v₀ j (lt_of_lt_of_le hi hk))
      (fun i hi => Finset.mem_coe.mpr (hUβ j i (hi.trans hk)))
  -- the exceptional edge
  obtain ⟨u₀, w₀, hdisj⟩ : ∃ u₀ w₀ : Port Node Term, ∀ e ∈ L.edges,
      s(e.1, e.2) ≠ s(u₀, w₀) → Disjoint Γ₀ (L.cl β y θ e) := by
    by_cases hex : ∃ e₀ ∈ L.edges, ¬ Disjoint Γ₀ (L.cl β y θ e₀)
    · obtain ⟨e₀, he₀, hnd⟩ := hex
      refine ⟨e₀.1, e₀.2, fun e he hne => ?_⟩
      have hee : e ≠ e₀ := fun h => hne (by rw [h])
      obtain ⟨q, hq1, hq2⟩ := Finset.not_disjoint_iff.mp hnd
      refine Finset.disjoint_left.mpr (fun z hz1 hz2 => ?_)
      rw [hΓ₀def] at hz1 hq1
      have hz := (mem_finiteBoxCluster θ _ _ _).mp hz1
      have hq := (mem_finiteBoxCluster θ _ _ _).mp hq1
      have hq' := (mem_finiteBoxCluster θ _ _ _).mp hq2
      have hz0 : z ∈ L.cl β y θ e₀ :=
        (mem_finiteBoxCluster θ _ _ _).mpr ⟨hz.1, hq'.2.trans (hq.2.symm.trans hz.2)⟩
      exact Finset.disjoint_left.mp (L.real_cl_disjoint hθ he he₀ hee) hz2 hz0
    · refine ⟨Port.root, Port.root, fun e he _ => ?_⟩
      by_contra hnd
      exact hex ⟨e, he, hnd⟩
  -- lifting
  have hFnotouch : ∀ b ∈ F, b ∉ touchBonds (L.Rm β) := by
    intro b hb htouch
    obtain ⟨j, k, hk, rfl⟩ := (hFmem b).mp hb
    rcases (mem_touchBonds _ _).mp htouch with h | h
    · exact hfar j k hk.le h
    · exact hfar j (k + 1) hk h
  have hlift : ∀ P Q, L.portGraph.Adj P Q → s(P, Q) ≠ s(u₀, w₀) →
      (restrictedGraph (closeBonds θ F) (L.Λ : Set (Vertex d))).Reachable
        (L.pos β y P) (L.pos β y Q) := by
    have hedge : ∀ e ∈ L.edges, s(e.1, e.2) ≠ s(u₀, w₀) →
        (restrictedGraph (closeBonds θ F) (L.Λ : Set (Vertex d))).Reachable
          (L.pos β y e.1) (L.pos β y e.2) := by
      intro e he hne
      obtain ⟨haT, z, hz, _, ⟨π⟩⟩ := L.real_edge_conn hθ he
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hTU : L.tube e ∩ (L.Uout β : Set (Vertex d)) ⊆ (L.Uout β : Set (Vertex d)) :=
        Set.inter_subset_right
      have hgood := walk_support_mem_cluster hTU haT π
      have hreach := reachable_of_walk_good (θ := closeBonds θ F)
        (fun z => z ∈ L.cl β y θ e) (fun b _ _ hg1 _ hbo => by
          refine closeBonds_of_notMem (fun hbF => ?_) hbo
          obtain ⟨j, k, hk, rfl⟩ := (hFmem b).mp hbF
          exact Finset.disjoint_left.mp (hdisj e he hne) (hΓ₀ j k hk.le) hg1) π hgood
      refine Reachable.mono (restrictedGraph_mono _ ?_) hreach
      exact fun z hz => Finset.mem_coe.mpr (Finset.mem_sdiff.mp (Finset.mem_coe.mp hz.2)).1
    have harms : ∀ v j, (restrictedGraph (closeBonds θ F) (L.Λ : Set (Vertex d))).Reachable
        (β v) (rayPt (β v) (L.ax j) L.R) := by
      intro v j
      refine arm_reachable (β v) (L.ax j) L.R (fun k hk => ?_)
        (fun k hk => Finset.mem_coe.mpr (hΛβ v j k hk))
      refine closeBonds_of_notMem (fun hbF => hFnotouch _ hbF ?_) (L.real_arm_open hθ v j hk)
      exact (mem_touchBonds _ _).mpr (Or.inl (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩⟩))
    intro P Q hadj hne
    obtain ⟨_, hrel⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    rcases hrel with (he | ⟨v, j, j', rfl, rfl⟩) | (he | ⟨v, j, j', rfl, rfl⟩)
    · exact hedge (P, Q) he hne
    · exact (harms v j).symm.trans (harms v j')
    · exact (hedge (Q, P) he (by rw [Sym2.eq_swap]; exact hne)).symm
    · exact (harms v j').symm.trans (harms v j)
  -- the sides of `β'`
  obtain ⟨A, hAdef⟩ : ∃ A : Fin 3 → Set (Vertex d), A = fun k =>
      {z | (∃ e ∈ L.edges, sideE e = k ∧ z ∈ L.cl β' y θ e) ∨
        (∃ u : Node, u ≠ v₀ ∧ sideN u = k ∧ ∃ (j : Fin 3) (i : ℕ), i < L.R ∧
          z = rayPt (β' u) (L.ax j) i)} := ⟨_, rfl⟩
  have harmRm : ∀ (u : Node) (j : Fin 3) (i : ℕ), i < L.R →
      rayPt (β' u) (L.ax j) i ∈ L.Rm β' := fun u j i hi =>
    Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩⟩⟩
  have hclU : ∀ e z, z ∈ L.cl β' y θ e → z ∉ L.Rm β' := fun e z hz =>
    (Finset.mem_sdiff.mp ((mem_finiteBoxCluster θ _ _ _).mp hz).1).2
  have hAdisj : ∀ k l : Fin 3, k ≠ l → ∀ z, z ∈ A k → z ∈ A l → False := by
    intro k l hkl z hk hl
    rw [hAdef] at hk hl
    rcases hk with ⟨e, he, hse, hz⟩ | ⟨u, _, hsu, j, i, hi, rfl⟩
    · rcases hl with ⟨e', he', hse', hz'⟩ | ⟨u', _, _, j', i', hi', rfl⟩
      · have hne : e ≠ e' := fun h => hkl (by rw [← hse, ← hse', h])
        exact Finset.disjoint_left.mp (L.real_cl_disjoint hθ' he he' hne) hz hz'
      · exact hclU e _ hz (harmRm u' j' i' hi')
    · rcases hl with ⟨e', he', hse', hz'⟩ | ⟨u', _, hsu', j', i', hi', heq⟩
      · exact hclU e' _ hz' (harmRm u j i hi)
      · have hne : u ≠ u' := fun h => hkl (by rw [← hsu, ← hsu', h])
        exact hsep' u u' hne j j' i i' hi hi' heq
  have htipA : ∀ (u : Node), u ≠ v₀ → ∀ j : Fin 3, rayPt (β' u) (L.ax j) L.R ∈ A (sideN u) := by
    intro u hu j
    obtain ⟨e, he, hport⟩ := htipedge u j
    have hmem := L.real_ports_mem_cl hθ' he
    rw [hAdef]
    refine Or.inl ⟨e, he, hside e he u j hport hu, ?_⟩
    rcases hport with h | h
    · have := hmem.1
      rw [h] at this
      exact this
    · have := hmem.2
      rw [h] at this
      exact this
  have hclosed : ∀ (k : Fin 3) (z w : Vertex d), z ∈ A k →
      (restrictedGraph (closeBonds θ F) (L.Λ : Set (Vertex d))).Adj z w → w ∈ A k := by
    intro k z w hz hadj
    obtain ⟨⟨b, hb, hends⟩, hzΛ, hwΛ⟩ := hadj
    obtain ⟨hbF, hbθ⟩ := closeBonds_true hb
    by_cases htouch : b ∈ touchBonds (L.Rm β')
    · -- a star bond of another node
      have hpat := hθ'.1 b htouch
      rw [hbθ] at hpat
      have hbSt : b ∈ L.St β' := of_decide_eq_true hpat.symm
      obtain ⟨u, _, hbu⟩ := Finset.mem_biUnion.mp hbSt
      obtain ⟨j, _, hbj⟩ := Finset.mem_biUnion.mp hbu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hbj
      have hiR := Finset.mem_range.mp hi
      have hu : u ≠ v₀ := by
        rintro rfl
        exact hbF ((hFmem _).mpr ⟨j, i, hiR, rfl⟩)
      have h1 : rayPt (β' u) (L.ax j) i ∈ A (sideN u) := by
        rw [hAdef]
        exact Or.inr ⟨u, hu, rfl, j, i, hiR, rfl⟩
      have h2 : rayPt (β' u) (L.ax j) (i + 1) ∈ A (sideN u) := by
        rcases Nat.lt_or_ge (i + 1) L.R with h | h
        · rw [hAdef]
          exact Or.inr ⟨u, hu, rfl, j, i + 1, h, rfl⟩
        · have hR : i + 1 = L.R := by omega
          rw [hR]
          exact htipA u hu j
      have hk : k = sideN u := by
        by_contra hne
        rcases hends with ⟨hz1, _⟩ | ⟨_, hz2⟩
        · exact hAdisj k (sideN u) hne z hz (by rw [hz1]; exact h1)
        · exact hAdisj k (sideN u) hne z hz (by rw [hz2]; exact h2)
      rw [hk]
      rcases hends with ⟨_, hw2⟩ | ⟨hw1, _⟩
      · rw [hw2]
        exact h2
      · rw [hw1]
        exact h1
    · -- an outside bond of `β'`
      have hnot := (mem_touchBonds _ _).not.mp htouch
      push_neg at hnot
      have hzU : z ∈ L.Uout β' := by
        rcases hends with ⟨hz1, _⟩ | ⟨_, hz2⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hzΛ, by rw [hz1]; exact hnot.1⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hzΛ, by rw [hz2]; exact hnot.2⟩
      have hwU : w ∈ L.Uout β' := by
        rcases hends with ⟨_, hw2⟩ | ⟨hw1, _⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hwΛ, by rw [hw2]; exact hnot.2⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hwΛ, by rw [hw1]; exact hnot.1⟩
      have hadjU : (restrictedGraph θ (L.Uout β' : Set (Vertex d))).Adj z w :=
        ⟨⟨b, hbθ, hends⟩, Finset.mem_coe.mpr hzU, Finset.mem_coe.mpr hwU⟩
      rw [hAdef] at hz ⊢
      rcases hz with ⟨e, he, hse, hze⟩ | ⟨u, _, _, j, i, hi, rfl⟩
      · have hzm := (mem_finiteBoxCluster θ _ _ _).mp hze
        exact Or.inl ⟨e, he, hse,
          (mem_finiteBoxCluster θ _ _ _).mpr ⟨hwU, hzm.2.trans hadjU.reachable⟩⟩
      · exact absurd (harmRm u j i hi) (Finset.mem_sdiff.mp hzU).2
  have hlab : ∀ z w, (restrictedGraph (closeBonds θ F) (L.Λ : Set (Vertex d))).Adj z w →
      ((z ∈ A 0, z ∈ A 1, z ∈ A 2) : Prop × Prop × Prop) = (w ∈ A 0, w ∈ A 1, w ∈ A 2) := by
    intro z w hadj
    have hiff : ∀ k : Fin 3, (z ∈ A k) = (w ∈ A k) := fun k =>
      propext ⟨fun h => hclosed k z w h hadj, fun h => hclosed k w z h hadj.symm⟩
    rw [hiff 0, hiff 1, hiff 2]
  -- the three ports
  have hTA : ∀ k : Fin 3, L.pos β y (Tk k) ∈ A k := by
    intro k
    obtain ⟨hmemE, hport, hsk⟩ := hek k
    have hmem := L.real_ports_mem_cl hθ' hmemE
    rw [hTk k, hAdef]
    refine Or.inl ⟨ek k, hmemE, hsk, ?_⟩
    rcases hport with h | h
    · have := hmem.1
      rw [h] at this
      exact this
    · have := hmem.2
      rw [h] at this
      exact this
  have hne : ∀ k l : Fin 3, k ≠ l → L.pos β y (Tk k) ∉ A l :=
    fun k l hkl h => hAdisj k l hkl _ (hTA k) h
  refine overcount_contradiction L.portGraph hT
    (restrictedGraph (closeBonds θ F) (L.Λ : Set (Vertex d))) (L.pos β y) u₀ w₀ hlift
    (fun z => ((z ∈ A 0, z ∈ A 1, z ∈ A 2) : Prop × Prop × Prop)) hlab (Tk 0) (Tk 1) (Tk 2)
    ?_ ?_ ?_
  · intro h
    have h1 : (L.pos β y (Tk 0) ∈ A 1) = (L.pos β y (Tk 1) ∈ A 1) := congrArg (fun t => t.2.1) h
    exact hne 0 1 (by decide) (h1 ▸ hTA 1)
  · intro h
    have h1 : (L.pos β y (Tk 0) ∈ A 2) = (L.pos β y (Tk 2) ∈ A 2) := congrArg (fun t => t.2.2) h
    exact hne 0 2 (by decide) (h1 ▸ hTA 2)
  · intro h
    have h1 : (L.pos β y (Tk 1) ∈ A 2) = (L.pos β y (Tk 2) ∈ A 2) := congrArg (fun t => t.2.2) h
    exact hne 1 2 (by decide) (h1 ▸ hTA 2)

end Layout

end NearCritical.SplitCrossDirect
end
