module
public import NearCritical.Section8FiveDiagrams

/-! Actual two-path decomposition used in the Section 8 expectation proofs.
Intersecting heart paths give a tripod; separated paths give disjoint occurrence. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

theorem annulusTau_comm {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d)) (x y : Vertex d) :
    annulusTau p Q H x y = annulusTau p Q H y x := by
  have he : annulusLink Q H x y = annulusLink Q H y x := by
    ext ω
    constructor
    · rintro ⟨hx,z,hz,hzD,hxz⟩
      have hzy : z = y := hz
      subst z
      exact ⟨hzD,x,rfl,hx,hxz.symm⟩
    · rintro ⟨hy,z,hz,hzD,hyz⟩
      have hzx : z = x := hz
      subst z
      exact ⟨hzD,y,rfl,hy,hyz.symm⟩
  unfold annulusTau
  rw [he]

private lemma reverse_edges_left {d : ℕ} {ω : Configuration d} {x a y b : Vertex d}
    {p : (openGraph ω).Walk x a} {q : (openGraph ω).Walk y b}
    (h : p.edges.Disjoint q.edges) : p.reverse.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e he hq
  exact List.disjoint_left.mp h
    (by simpa only [SimpleGraph.Walk.edges_reverse,List.mem_reverse] using he) hq

private lemma reverse_edges_right {d : ℕ} {ω : Configuration d} {x a y b : Vertex d}
    {p : (openGraph ω).Walk x a} {q : (openGraph ω).Walk y b}
    (h : p.edges.Disjoint q.edges) : p.edges.Disjoint q.reverse.edges :=
  (reverse_edges_left h.symm).symm

private lemma actual_heart_path {d : ℕ} {ω : Configuration d} (Q H : Finset (Vertex d))
    (x : Vertex d) (hx : x ∈ heartAnnulus Q H) (he : ω ∈ heartEvent Q H x) :
    ∃ a ∈ boundarySites H, ∃ w : (openGraph ω).Walk x a,
      w.IsPath ∧ ∀ v ∈ w.support, v ∈ heartAnnulus Q H := by
  rw [heartEvent_eq_annulus Q H x hx] at he
  obtain ⟨hxD,a,ha,_haD,⟨w⟩⟩ := he
  have hle : restrictedGraph ω (heartAnnulus Q H : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
  let r : (openGraph ω).Walk x a :=
    (w.toPath : (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Walk x a).mapLe hle
  refine ⟨a,ha,r,w.toPath.property.mapLe hle,?_⟩
  intro v hv
  exact restrictedWalk_support
    (w.toPath : (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Walk x a) hxD v
    (by simpa only [r,SimpleGraph.Walk.support_mapLe_eq_support] using hv)

private lemma tripod_occurrence {d : ℕ} {ω : Configuration d} (D : Finset (Vertex d))
    (R : Set (Vertex d)) {u a x y : Vertex d}
    (w₀ : (openGraph ω).Walk u a) (w₁ : (openGraph ω).Walk u x) (w₂ : (openGraph ω).Walk u y)
    (hD₀ : ∀ v ∈ w₀.support, v ∈ D) (hD₁ : ∀ v ∈ w₁.support, v ∈ D)
    (hD₂ : ∀ v ∈ w₂.support, v ∈ D) (ha : a ∈ R)
    (h₀₁ : w₀.edges.Disjoint w₁.edges) (h₀₂ : w₀.edges.Disjoint w₂.edges)
    (h₁₂ : w₁.edges.Disjoint w₂.edges) :
    DisjointOccurrence (connectionToSetEvent (D : Set (Vertex d)) u R)
      {θ | DisjointOccurrence (connectionToSetEvent (D : Set (Vertex d)) u {x})
        (connectionToSetEvent (D : Set (Vertex d)) u {y}) θ} ω := by
  obtain ⟨F₀,ho₀,he₀,hf₀⟩ := openWalk_certificate w₀ (D : Set (Vertex d)) hD₀
  obtain ⟨F₁,ho₁,he₁,hf₁⟩ := openWalk_certificate w₁ (D : Set (Vertex d)) hD₁
  obtain ⟨F₂,ho₂,he₂,hf₂⟩ := openWalk_certificate w₂ (D : Set (Vertex d)) hD₂
  have hd₀₁ : Disjoint (F₀ : Set (Bond d)) (F₁ : Set (Bond d)) :=
    Set.disjoint_left.mpr (fun e h0 h1 => List.disjoint_left.mp h₀₁ (he₀ e h0) (he₁ e h1))
  have hd₀₂ : Disjoint (F₀ : Set (Bond d)) (F₂ : Set (Bond d)) :=
    Set.disjoint_left.mpr (fun e h0 h2 => List.disjoint_left.mp h₀₂ (he₀ e h0) (he₂ e h2))
  have hd₁₂ : Disjoint (F₁ : Set (Bond d)) (F₂ : Set (Bond d)) :=
    Set.disjoint_left.mpr (fun e h1 h2 => List.disjoint_left.mp h₁₂ (he₁ e h1) (he₂ e h2))
  have hF₁ : ForcesOn (connectionToSetEvent (D : Set (Vertex d)) u {x}) ω (F₁ : Set (Bond d)) :=
    fun θ hθ => hf₁ θ (fun e he => (hθ e he).trans (ho₁ e he))
  have hF₂ : ForcesOn (connectionToSetEvent (D : Set (Vertex d)) u {y}) ω (F₂ : Set (Bond d)) :=
    fun θ hθ => hf₂ θ (fun e he => (hθ e he).trans (ho₂ e he))
  refine ⟨(F₀ : Set (Bond d)),(F₁ : Set (Bond d)) ∪ (F₂ : Set (Bond d)),
    F₀.finite_toSet,F₁.finite_toSet.union F₂.finite_toSet,?_,?_,
    forcesOn_disjointOccurrence_union F₁.finite_toSet F₂.finite_toSet hd₁₂ hF₁ hF₂⟩
  · apply Set.disjoint_left.mpr
    intro e he0 he
    rcases he with he1 | he2
    · exact Set.disjoint_left.mp hd₀₁ he0 he1
    · exact Set.disjoint_left.mp hd₀₂ he0 he2
  · intro θ hθ
    obtain ⟨huD,z,hz,hzD,huz⟩ := hf₀ θ (fun e he => (hθ e he).trans (ho₀ e he))
    have hza : z = a := hz
    subst z
    exact ⟨huD,a,ha,hzD,huz⟩

private lemma increasing_occurrence {E : Type*} {A B : Set (E → Bool)}
    (hA : BK.Increasing A) (hB : BK.Increasing B) :
    BK.Increasing {ω | DisjointOccurrence A B ω} := by
  intro ω η h hω
  obtain ⟨F,G,hFfin,hGfin,hdis,hF,hG,hAF,hBG⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence hω
  exact BK.OpenDisjointOccurrence.to_disjointOccurrence
    ⟨F,G,hFfin,hGfin,hdis,(fun e he => h e (hF e he)),
      (fun e he => h e (hG e he)),hAF,hBG⟩ hA hB

/-- The actual pair-membership tree bound used in Ef1/Ef2. The branch point
is obtained from actual paths; its probability product is derived by BK. -/
theorem heartPair_probability_le_annulus_tree {d : ℕ} (p : unitInterval)
    (Q H : Finset (Vertex d)) (x y : Vertex d)
    (hx : x ∈ heartAnnulus Q H) (hy : y ∈ heartAnnulus Q H) :
    (percolation d p).real (heartPairEvent Q H x y) ≤
      annulusG p Q H x*annulusG p Q H y +
        ∑ u ∈ heartAnnulus Q H, annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u y := by
  let D := heartAnnulus Q H
  let R : Set (Vertex d) := (boundarySites H : Set (Vertex d))
  let A : Set (Configuration d) := {ω | DisjointOccurrence (annulusHit Q H x) (annulusHit Q H y) ω}
  let T (u : Vertex d) : Set (Configuration d) :=
    {ω | DisjointOccurrence (annulusHit Q H u)
      {θ | DisjointOccurrence (annulusLink Q H u x) (annulusLink Q H u y) θ} ω}
  have hsub : heartPairEvent Q H x y ⊆ A ∪ ⋃ u ∈ D, T u := by
    intro ω hω
    obtain ⟨a,ha,wx,hwx,hxD⟩ := actual_heart_path Q H x hx hω.1
    obtain ⟨b,hb,wy,_hwy,hyD⟩ := actual_heart_path Q H y hy hω.2
    by_cases hint : ∃ v ∈ wy.support, v ∈ wx.support
    · obtain ⟨u,px,qx,py,qy,hxsplit,hysplit,hpq,hrp,hrq,_hfirst⟩ := first_hit_tripod wx hwx wy hint
      have hpxD : ∀ v ∈ px.support, v ∈ D := by
        intro v hv
        apply hxD v
        rw [← hxsplit]
        exact px.support_subset_support_append_left qx hv
      have hqxD : ∀ v ∈ qx.support, v ∈ D := by
        intro v hv
        apply hxD v
        rw [← hxsplit]
        exact px.support_subset_support_append_right qx hv
      have hpyD : ∀ v ∈ py.support, v ∈ D := by
        intro v hv
        apply hyD v
        rw [← hysplit]
        exact py.support_subset_support_append_left qy hv
      have hu : u ∈ D := hqxD u qx.start_mem_support
      have ht : ω ∈ T u := tripod_occurrence D R qx px.reverse py.reverse hqxD
        (fun v hv => hpxD v (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv))
        (fun v hv => hpyD v (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv))
        ha (reverse_edges_right hpq.symm) (reverse_edges_right hrq.symm)
        (reverse_edges_left (reverse_edges_right hrp.symm))
      exact Or.inr (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,ht⟩⟩)
    · have hdis : wx.edges.Disjoint wy.edges := by
        apply walk_edges_disjoint_of_one_common_vertex (u := x)
        intro v hvx hvy
        exact (hint ⟨v,hvy,hvx⟩).elim
      exact Or.inl (disjointOpenWalks_occurrence wx wy hdis (D : Set (Vertex d))
        (D : Set (Vertex d)) R R hxD hyD ha hb)
  have hA : (percolation d p).real A ≤ annulusG p Q H x*annulusG p Q H y :=
    percolation_bk d p (annulusHit Q H x) (annulusHit Q H y)
      (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
  have hT (u : Vertex d) : (percolation d p).real (T u) ≤
      annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u y := by
    let B : Set (Configuration d) :=
      {θ | DisjointOccurrence (annulusLink Q H u x) (annulusLink Q H u y) θ}
    have hb : BK.Increasing B := increasing_occurrence
      (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
    calc
      _ ≤ annulusG p Q H u*(percolation d p).real B :=
        percolation_bk d p (annulusHit Q H u) B (connectionToSetEvent_increasing _ _ _) hb
      _ ≤ annulusG p Q H u*(annulusTau p Q H u x*annulusTau p Q H u y) :=
        mul_le_mul_of_nonneg_left (percolation_bk d p (annulusLink Q H u x) (annulusLink Q H u y)
          (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)) measureReal_nonneg
      _ = _ := by ring
  calc
    _ ≤ (percolation d p).real (A ∪ ⋃ u ∈ D, T u) := measureReal_mono hsub
    _ ≤ (percolation d p).real A+(percolation d p).real (⋃ u ∈ D, T u) := measureReal_union_le _ _
    _ ≤ annulusG p Q H x*annulusG p Q H y +
        ∑ u ∈ D, annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u y :=
      add_le_add hA ((measureReal_biUnion_finset_le D T).trans (Finset.sum_le_sum (fun u _hu => hT u)))

end NearCritical.Section8
