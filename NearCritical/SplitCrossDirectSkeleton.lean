module

public import NearCritical.Events
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Skeletons (item B of the direct proof of `SplitCrossInput`, deterministic
half): the root-branch decomposition of a vertex joined to several targets.

`Skel G y u S E W`: a tree-shaped certificate that `u` is joined to every
terminal `y i`, `i ∈ S` (a finite set of labels; terminals may coincide), in
the graph `G`, with edge set `E` and vertex set `W`.
* `leaf`: a path from `u` to the single terminal;
* `branch`: a path from `u` to a branch vertex `w` followed by two skeletons
  rooted at `w` on two disjoint nonempty label sets, the three pieces pairwise
  edge-disjoint.

`Skel.insert`: a skeleton and an edge-disjoint path from one of its vertices to
a new terminal give a skeleton with that terminal added.
`exists_skel`: if `u` is joined to every terminal of a nonempty label set, a
skeleton exists (insert the terminals one at a time, cutting the path from the
new terminal at its first hit of the current skeleton).

This is the deterministic input of the `n`-point tree-graph recursion; the
existing code has only the two-terminal case (the tripod).
-/
@[expose] public section
namespace NearCritical.SplitCrossDirect
open SimpleGraph
open scoped Classical

variable {V ι : Type*}

inductive Skel (G : SimpleGraph V) (y : ι → V) : V → Finset ι → Set (Sym2 V) → Set V → Prop
  | leaf {u : V} (i : ι) (p : G.Walk u (y i)) (hp : p.IsPath) :
      Skel G y u {i} {e | e ∈ p.edges} {x | x ∈ p.support}
  | branch {u w : V} {A B : Finset ι} {EA EB : Set (Sym2 V)} {WA WB : Set V}
      (p : G.Walk u w) (hp : p.IsPath) (hA : Skel G y w A EA WA) (hB : Skel G y w B EB WB)
      (d1 : ∀ e ∈ p.edges, e ∉ EA) (d2 : ∀ e ∈ p.edges, e ∉ EB) (d3 : Disjoint EA EB)
      (hAB : Disjoint A B) :
      Skel G y u (A ∪ B) (({e | e ∈ p.edges} ∪ EA) ∪ EB) (({x | x ∈ p.support} ∪ WA) ∪ WB)

variable {G : SimpleGraph V} {y : ι → V}

theorem Skel.root_mem {u : V} {S : Finset ι} {E : Set (Sym2 V)} {W : Set V}
    (h : Skel G y u S E W) : u ∈ W := by
  induction h with
  | leaf i p hp => exact p.start_mem_support
  | branch p hp hA hB d1 d2 d3 hAB ihA ihB => exact Or.inl (Or.inl p.start_mem_support)

theorem Skel.nonempty {u : V} {S : Finset ι} {E : Set (Sym2 V)} {W : Set V}
    (h : Skel G y u S E W) : S.Nonempty := by
  induction h with
  | leaf i p hp => exact Finset.singleton_nonempty i
  | branch p hp hA hB d1 d2 d3 hAB ihA ihB => exact ihA.mono Finset.subset_union_left

theorem Skel.edge_ends {u : V} {S : Finset ι} {E : Set (Sym2 V)} {W : Set V}
    (h : Skel G y u S E W) : ∀ a b : V, s(a, b) ∈ E → a ∈ W ∧ b ∈ W := by
  induction h with
  | leaf i p hp =>
    intro a b he
    exact ⟨p.fst_mem_support_of_mem_edges he, p.snd_mem_support_of_mem_edges he⟩
  | branch p hp hA hB d1 d2 d3 hAB ihA ihB =>
    intro a b he
    rcases he with (he | he) | he
    · exact ⟨Or.inl (Or.inl (p.fst_mem_support_of_mem_edges he)),
        Or.inl (Or.inl (p.snd_mem_support_of_mem_edges he))⟩
    · exact ⟨Or.inl (Or.inr (ihA a b he).1), Or.inl (Or.inr (ihA a b he).2)⟩
    · exact ⟨Or.inr (ihB a b he).1, Or.inr (ihB a b he).2⟩

lemma walk_support_subset_of_closed {D : Set V} (hD : ∀ a b, G.Adj a b → a ∈ D → b ∈ D) :
    ∀ {a b : V} (p : G.Walk a b), a ∈ D → ∀ x ∈ p.support, x ∈ D := by
  intro a b p
  induction p with
  | nil =>
    intro ha x hx
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ha
  | @cons a c b hac p ih =>
    intro ha x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih (hD _ _ hac ha) x hx

/-- In a graph whose edges do not leave `D`, a skeleton rooted in `D` stays in `D`. -/
theorem Skel.subset_of_closed {D : Set V} (hD : ∀ a b, G.Adj a b → a ∈ D → b ∈ D)
    {u : V} {S : Finset ι} {E : Set (Sym2 V)} {W : Set V}
    (h : Skel G y u S E W) : u ∈ D → W ⊆ D := by
  induction h with
  | leaf i p hp => exact fun hu x hx => walk_support_subset_of_closed hD p hu x hx
  | branch p hp hA hB d1 d2 d3 hAB ihA ihB =>
    intro hu x hx
    have hw := walk_support_subset_of_closed hD p hu _ p.end_mem_support
    rcases hx with (hx | hx) | hx
    · exact walk_support_subset_of_closed hD p hu x hx
    · exact ihA hw hx
    · exact ihB hw hx

/-- Skeletons pass to larger graphs. -/
theorem Skel.mono {G' : SimpleGraph V} (hle : G ≤ G') {u : V} {S : Finset ι}
    {E : Set (Sym2 V)} {W : Set V} (h : Skel G y u S E W) : Skel G' y u S E W := by
  induction h with
  | leaf i p hp =>
    have h := Skel.leaf (G := G') (y := y) i (p.mapLe hle) (hp.mapLe hle)
    simpa only [Walk.edges_mapLe_eq_edges, Walk.support_mapLe_eq_support] using h
  | branch p hp hA hB d1 d2 d3 hAB ihA ihB =>
    have h := Skel.branch (p.mapLe hle) (hp.mapLe hle) ihA ihB
      (by simpa only [Walk.edges_mapLe_eq_edges] using d1)
      (by simpa only [Walk.edges_mapLe_eq_edges] using d2) d3 hAB
    simpa only [Walk.edges_mapLe_eq_edges, Walk.support_mapLe_eq_support] using h

lemma split_edges_disjoint {u w v : V} {p : G.Walk u w} (hp : p.IsPath) (hv : v ∈ p.support) :
    ∀ e ∈ (p.takeUntil v hv).edges, e ∉ (p.dropUntil v hv).edges := by
  have hnd := hp.isTrail.edges_nodup
  rw [← p.take_spec hv, Walk.edges_append] at hnd
  intro e he1 he2
  exact (List.nodup_append.mp hnd).2.2 e he1 e he2 rfl

theorem Skel.insert {u : V} {S : Finset ι} {E : Set (Sym2 V)} {W : Set V}
    (h : Skel G y u S E W) : ∀ {v : V} {j : ι}, j ∉ S → v ∈ W → ∀ (π : G.Walk v (y j)),
      π.IsPath → (∀ e ∈ π.edges, e ∉ E) →
      ∃ (E' : Set (Sym2 V)) (W' : Set V), Skel G y u (insert j S) E' W' ∧
        E' ⊆ E ∪ {e | e ∈ π.edges} := by
  induction h with
  | @leaf u i p hp =>
    intro v j hj hv π hπ hd
    have hv' : v ∈ p.support := hv
    have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_singleton_self _)
    have hsk := Skel.branch (p.takeUntil v hv') (hp.takeUntil hv')
      (Skel.leaf j π hπ) (Skel.leaf i (p.dropUntil v hv') (hp.dropUntil hv'))
      (fun e he hπe => hd e hπe (p.edges_takeUntil_subset_edges hv' he))
      (split_edges_disjoint hp hv')
      (Set.disjoint_left.mpr (fun e hπe he =>
        hd e hπe (p.edges_dropUntil_subset_edges hv' he)))
      (Finset.disjoint_singleton.mpr hji)
    rw [← Finset.insert_eq] at hsk
    refine ⟨_, _, hsk, ?_⟩
    rintro e ((he | he) | he)
    · exact Or.inl (p.edges_takeUntil_subset_edges hv' he)
    · exact Or.inr he
    · exact Or.inl (p.edges_dropUntil_subset_edges hv' he)
  | @branch u w A B EA EB WA WB p hp hA hB d1 d2 d3 hAB ihA ihB =>
    intro v j hj hv π hπ hd
    have hjA : j ∉ A := fun h => hj (Finset.mem_union_left _ h)
    have hjB : j ∉ B := fun h => hj (Finset.mem_union_right _ h)
    rcases hv with (hv | hv) | hv
    · have hv' : v ∈ p.support := hv
      have hsk := Skel.branch (p.takeUntil v hv') (hp.takeUntil hv') (Skel.leaf j π hπ)
        (Skel.branch (p.dropUntil v hv') (hp.dropUntil hv') hA hB
          (fun e he => d1 e (p.edges_dropUntil_subset_edges hv' he))
          (fun e he => d2 e (p.edges_dropUntil_subset_edges hv' he)) d3 hAB)
        (fun e he hπe =>
          hd e hπe (Or.inl (Or.inl (p.edges_takeUntil_subset_edges hv' he))))
        (by
          rintro e he ((h2 | h2) | h2)
          · exact split_edges_disjoint hp hv' e he h2
          · exact d1 e (p.edges_takeUntil_subset_edges hv' he) h2
          · exact d2 e (p.edges_takeUntil_subset_edges hv' he) h2)
        (Set.disjoint_left.mpr (by
          rintro e hπe ((h2 | h2) | h2)
          · exact hd e hπe (Or.inl (Or.inl (p.edges_dropUntil_subset_edges hv' h2)))
          · exact hd e hπe (Or.inl (Or.inr h2))
          · exact hd e hπe (Or.inr h2)))
        (Finset.disjoint_singleton_left.mpr hj)
      rw [← Finset.insert_eq] at hsk
      refine ⟨_, _, hsk, ?_⟩
      rintro e ((he | he) | ((he | he) | he))
      · exact Or.inl (Or.inl (Or.inl (p.edges_takeUntil_subset_edges hv' he)))
      · exact Or.inr he
      · exact Or.inl (Or.inl (Or.inl (p.edges_dropUntil_subset_edges hv' he)))
      · exact Or.inl (Or.inl (Or.inr he))
      · exact Or.inl (Or.inr he)
    · obtain ⟨EA', WA', hskA, hsub⟩ :=
        ihA hjA hv π hπ (fun e he hE => hd e he (Or.inl (Or.inr hE)))
      have hsk := Skel.branch p hp hskA hB
        (fun e he hE' => by
          rcases hsub hE' with h2 | h2
          · exact d1 e he h2
          · exact hd e h2 (Or.inl (Or.inl he)))
        d2
        (Set.disjoint_left.mpr (fun e hE' hEB => by
          rcases hsub hE' with h2 | h2
          · exact Set.disjoint_left.mp d3 h2 hEB
          · exact hd e h2 (Or.inr hEB)))
        (Finset.disjoint_insert_left.mpr ⟨hjB, hAB⟩)
      rw [Finset.insert_union] at hsk
      refine ⟨_, _, hsk, ?_⟩
      rintro e ((he | he) | he)
      · exact Or.inl (Or.inl (Or.inl he))
      · rcases hsub he with h2 | h2
        · exact Or.inl (Or.inl (Or.inr h2))
        · exact Or.inr h2
      · exact Or.inl (Or.inr he)
    · obtain ⟨EB', WB', hskB, hsub⟩ :=
        ihB hjB hv π hπ (fun e he hE => hd e he (Or.inr hE))
      have hsk := Skel.branch p hp hA hskB d1
        (fun e he hE' => by
          rcases hsub hE' with h2 | h2
          · exact d2 e he h2
          · exact hd e h2 (Or.inl (Or.inl he)))
        (Set.disjoint_left.mpr (fun e hEA hE' => by
          rcases hsub hE' with h2 | h2
          · exact Set.disjoint_left.mp d3 hEA h2
          · exact hd e h2 (Or.inl (Or.inr hEA))))
        (Finset.disjoint_insert_right.mpr ⟨hjA, hAB⟩)
      rw [Finset.union_insert] at hsk
      refine ⟨_, _, hsk, ?_⟩
      rintro e ((he | he) | he)
      · exact Or.inl (Or.inl (Or.inl he))
      · exact Or.inl (Or.inl (Or.inr he))
      · rcases hsub he with h2 | h2
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h2

/-- First hit of a vertex set along a path. -/
lemma exists_first_hit {a b : V} (q : G.Walk a b) (W : Set V) (hb : b ∈ W) :
    ∃ v, ∃ h : v ∈ q.support, v ∈ W ∧ ∀ x ∈ (q.takeUntil v h).support, x ∈ W → x = v := by
  have H : ∃ n : ℕ, ∃ v, ∃ h : v ∈ q.support, v ∈ W ∧ (q.takeUntil v h).length = n :=
    ⟨_, b, q.end_mem_support, hb, rfl⟩
  obtain ⟨v, h, hvW, hlen⟩ := Nat.find_spec H
  refine ⟨v, h, hvW, fun x hx hxW => ?_⟩
  by_contra hne
  have hlt := Walk.length_takeUntil_lt_length hx hne
  rw [Walk.takeUntil_takeUntil] at hlt
  have hmin := Nat.find_min' H
    ⟨x, q.support_takeUntil_subset_support h hx, hxW, rfl⟩
  omega

/-- **Existence of a skeleton.** -/
theorem exists_skel (y : ι → V) (u : V) (S : Finset ι) (hS : S.Nonempty) :
    (∀ i ∈ S, G.Reachable u (y i)) → ∃ (E : Set (Sym2 V)) (W : Set V), Skel G y u S E W := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro hr
    obtain ⟨p, hp⟩ := (hr a (Finset.mem_singleton_self a)).exists_isPath
    exact ⟨_, _, Skel.leaf a p hp⟩
  | cons a s ha hs ih =>
    intro hr
    obtain ⟨E, W, hsk⟩ := ih (fun i hi => hr i (Finset.mem_cons.mpr (Or.inr hi)))
    obtain ⟨q, hq⟩ := (hr a (Finset.mem_cons_self a s)).symm.exists_isPath
    obtain ⟨v, hv, hvW, hfirst⟩ := exists_first_hit q W hsk.root_mem
    have hπ : ((q.takeUntil v hv).reverse).IsPath := (hq.takeUntil hv).reverse
    have hd : ∀ e ∈ ((q.takeUntil v hv).reverse).edges, e ∉ E := by
      intro e he hE
      rw [Walk.edges_reverse, List.mem_reverse] at he
      induction e using Sym2.ind with
      | _ b c =>
        obtain ⟨hbW, hcW⟩ := hsk.edge_ends b c hE
        have hb := hfirst b ((q.takeUntil v hv).fst_mem_support_of_mem_edges he) hbW
        have hc := hfirst c ((q.takeUntil v hv).snd_mem_support_of_mem_edges he) hcW
        have hadj := (q.takeUntil v hv).adj_of_mem_edges he
        rw [hb, hc] at hadj
        exact G.irrefl hadj
    obtain ⟨E', W', hsk', _⟩ := hsk.insert ha hvW _ hπ hd
    rw [Finset.cons_eq_insert]
    exact ⟨E', W', hsk'⟩

end NearCritical.SplitCrossDirect
