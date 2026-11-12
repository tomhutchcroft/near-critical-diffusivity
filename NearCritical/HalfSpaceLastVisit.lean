module

public import NearCritical.HalfSpaceArmGeometry

/-! Last-height decomposition for the new subcritical half-space arm argument. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Select the last vertex with a property in a finite walk. The suffix after
that vertex has no further occurrence of the property. -/
lemma walk_last_visit {V : Type*} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (P : V → Prop) (hex : ∃ u ∈ w.support, P u) :
    ∃ (u : V) (p : G.Walk x u) (q : G.Walk u y), p.append q = w ∧ P u ∧
      ∀ z ∈ q.support.tail, ¬ P z := by
  induction w with
  | @nil u =>
    have hx : P u := by simpa using hex
    exact ⟨_, .nil, .nil, rfl, hx, by simp⟩
  | @cons x z y h w ih =>
    by_cases htail : ∃ u ∈ w.support, P u
    · obtain ⟨u, p, q, hpq, hu, hlast⟩ := ih htail
      refine ⟨u, p.cons h, q, ?_, hu, hlast⟩
      simp only [SimpleGraph.Walk.cons_append, hpq]
    · have hx : P x := by
        obtain ⟨u, hu, hPu⟩ := hex
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hPu
        · exact False.elim (htail ⟨u, hu, hPu⟩)
      refine ⟨x, .nil, w.cons h, by simp, hx, ?_⟩
      intro u hu hPu
      exact htail ⟨u, hu, hPu⟩

/-- Actual lattice adjacency changes each coordinate by at most one. -/
lemma openGraph_adj_height_bounds {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (h : (openGraph ω).Adj x y) (i : Fin d) :
    x i ≤ y i + 1 ∧ y i ≤ x i + 1 := by
  obtain ⟨e, _, hends⟩ := h
  have he : e.1 i ≤ bondTip e i + 1 ∧ bondTip e i ≤ e.1 i + 1 := by
    by_cases hi : i = e.2
    · subst i
      simp only [bondTip, Function.update_self]
      omega
    · simp [bondTip, Function.update_of_ne hi]
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  · exact he.symm

/-- An integer-height nearest-neighbor walk crosses every intermediate level. -/
lemma openWalk_visits_height {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (w : (openGraph ω).Walk x y) (i : Fin d) (l : ℤ)
    (hx : x i ≤ l) (hy : l ≤ y i) :
    ∃ u ∈ w.support, u i = l := by
  induction w with
  | nil => exact ⟨_, by simp, le_antisymm hx hy⟩
  | @cons x z y h w ih =>
    by_cases heq : x i = l
    · exact ⟨x, by simp, heq⟩
    · have hz : z i ≤ l := by
        have hb := (openGraph_adj_height_bounds h i).2
        omega
      obtain ⟨u, hu, hul⟩ := ih hz hy
      exact ⟨u, by simp [hu], hul⟩

/-- If a walk ends above a level and avoids that level entirely, all its
vertices are strictly above it. -/
lemma openWalk_above_of_avoids_height {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (w : (openGraph ω).Walk x y) (i : Fin d) (l : ℤ)
    (hy : l ≤ y i) (havoid : ∀ z ∈ w.support, z i ≠ l) :
    ∀ z ∈ w.support, l < z i := by
  induction w with
  | @nil u =>
    intro z hz
    have hzy : z = u := by simpa using hz
    subst z
    exact lt_of_le_of_ne hy (Ne.symm (havoid _ (by simp)))
  | @cons x z y h w ih =>
    have ht : ∀ t ∈ w.support, l < t i :=
      ih hy (fun t ht ↦ havoid t (by simp [ht]))
    intro t ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · have hz := ht z w.start_mem_support
      have hb := (openGraph_adj_height_bounds h i).2
      have hn := havoid t (by simp)
      omega
    · exact ht t ht'

/-- After the last visit to a level, a walk ending above it stays above it. -/
lemma openWalk_suffix_above_height {d : ℕ} {ω : Configuration d} {u y : Vertex d}
    (q : (openGraph ω).Walk u y) (i : Fin d) (l : ℤ)
    (hu : u i = l) (hy : l ≤ y i)
    (hlast : ∀ z ∈ q.support.tail, z i ≠ l) :
    ∀ z ∈ q.support, l ≤ z i := by
  cases q with
  | nil => simp [hu]
  | @cons u z y h q =>
    have hq : ∀ t ∈ q.support, l < t i :=
      openWalk_above_of_avoids_height q i l hy (by simpa using hlast)
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hu.ge
    · exact (hq t ht).le

/-- Source Step 1's last-intermediate-level split, for an actual connection in
any vertex domain. The suffix stays above the selected level. -/
theorem connectionToSet_last_height_split {d : ℕ} {ω : Configuration d}
    (S B : Set (Vertex d)) (x : Vertex d) (i : Fin d) (l : ℤ)
    (hx : x i ≤ l) (hB : ∀ y ∈ B, l ≤ y i)
    (hω : ω ∈ connectionToSetEvent S x B) :
    ∃ u : Vertex d, u i = l ∧ DisjointOccurrence
      (connectionToSetEvent S x {u})
      (connectionToSetEvent (S ∩ {z | l ≤ z i}) u B) ω := by
  obtain ⟨hxS, y, hyB, _, ⟨w⟩⟩ := hω
  have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h ↦ h.1
  let r : (openGraph ω).Walk x y := (w.toPath : (restrictedGraph ω S).Walk x y).mapLe hle
  have hr : r.IsPath := w.toPath.property.mapLe _
  have hrS : ∀ z ∈ r.support, z ∈ S := by
    simpa only [r, SimpleGraph.Walk.support_mapLe_eq_support] using
      restrictedWalk_support (w.toPath : (restrictedGraph ω S).Walk x y) hxS
  obtain ⟨u, p, q, hpq, hul, hlast⟩ := walk_last_visit r (fun z ↦ z i = l)
    (openWalk_visits_height r i l hx (hB y hyB))
  have hdis : p.edges.Disjoint q.edges :=
    ((SimpleGraph.Walk.isTrail_append p q).mp (hpq.symm ▸ hr.isTrail)).2.2
  have hpS : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    apply hrS z
    rw [← hpq]
    exact p.support_subset_support_append_left q hz
  have hqS : ∀ z ∈ q.support, z ∈ S := by
    intro z hz
    apply hrS z
    rw [← hpq]
    exact p.support_subset_support_append_right q hz
  refine ⟨u, hul, disjointOpenWalks_occurrence p q hdis S
    (S ∩ {z | l ≤ z i}) {u} B hpS ?_ rfl hyB⟩
  intro z hz
  exact ⟨hqS z hz, openWalk_suffix_above_height q i l hul (hB y hyB) hlast z hz⟩

/-- The literal half-space last-level decomposition, with a target upper
half-space. Abstract integer cuts avoid any floor/ceiling identification. -/
theorem halfSpace_arm_last_height_split {d : ℕ} {ω : Configuration d}
    (i : Fin d) (a l n : ℤ) (x : Vertex d)
    (hal : a ≤ l) (hx : x i ≤ l) (hln : l ≤ n)
    (hω : ω ∈ connectionToSetEvent {z | a ≤ z i} x {z | n ≤ z i}) :
    ∃ u : Vertex d, u i = l ∧ DisjointOccurrence
      (connectionToSetEvent {z | a ≤ z i} x {u})
      (connectionToSetEvent {z | l ≤ z i} u {z | n ≤ z i}) ω := by
  obtain ⟨u, hul, hdis⟩ := connectionToSet_last_height_split
    {z | a ≤ z i} {z | n ≤ z i} x i l hx (fun y hy ↦ hln.trans hy) hω
  have heq : {z : Vertex d | a ≤ z i} ∩ {z | l ≤ z i} = {z | l ≤ z i} := by
    ext z
    constructor
    · exact fun hz ↦ hz.2
    · intro hz
      exact ⟨hal.trans hz, hz⟩
  exact ⟨u, hul, by simpa only [heq] using hdis⟩

end NearCritical
